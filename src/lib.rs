//! Read and write DWARF's "Little Endian Base 128" (LEB128) variable length
//! integer encoding.
//!
//! The implementation is a direct translation of the psuedocode in the DWARF 4
//! standard's appendix C.
//!
//! Read and write signed integers:
//!
//! ```
//! use leb128;
//!
//! let mut buf = [0; 1024];
//!
//! // Write to buf.
//! leb128::write::signed(&mut buf, -12345);
//!
//! // Read from buf.
//! let val = leb128::read::signed(&buf).0.expect("Should read number");
//! assert_eq!(val, -12345);
//! ```
//!
//! Or read and write unsigned integers:
//!
//! ```
//! use leb128;
//!
//! let mut buf = [0; 1024];
//!
//! leb128::write::unsigned(&mut buf, 98765);
//!
//! let val = leb128::read::unsigned(&buf).0.expect("Should read number");
//! assert_eq!(val, 98765);
//! ```

#![deny(missing_docs)]
#![no_std]

#[doc(hidden)]
pub const CONTINUATION_BIT: u8 = 1 << 7;
#[doc(hidden)]
pub const SIGN_BIT: u8 = 1 << 6;

#[doc(hidden)]
#[inline]
pub fn low_bits_of_byte(byte: u8) -> u8 {
    byte & !CONTINUATION_BIT
}

#[doc(hidden)]
#[inline]
pub fn low_bits_of_u64(val: u64) -> u8 {
    let byte = val & (core::u8::MAX as u64);
    low_bits_of_byte(byte as u8)
}

/// A module for reading LEB128-encoded signed and unsigned integers.
pub mod read {
    use super::{low_bits_of_byte, CONTINUATION_BIT, SIGN_BIT};
    use core::result::Result::{self, Ok, Err};
    use core::marker::Sized;

    /// Read an unsigned LEB128-encoded number from the buf
    ///
    /// On success, return the number.
    pub fn unsigned(buf: &mut &[u8]) -> (Result<u64, ()>, &[u8]) {
        let mut result = 0;
        let mut shift = 0;

        loop {
            let byte = (*buf)[0];
            if shift == 63 && byte != 0x00 && byte != 0x01 {
                while buf[0] & CONTINUATION_BIT != 0 {
                    buf = &buf[1..];
                }
                return (Err(()), buf);
            }
            *buf = &(*buf)[1..];

            let low_bits = low_bits_of_byte(byte) as u64;
            result |= low_bits << shift;

            if byte & CONTINUATION_BIT == 0 {
                return (Ok(result), buf);
            }

            shift += 7;
        }
    }

    /// Read a signed LEB128-encoded number from the buf
    ///
    /// On success, return the number.
    pub fn signed(buf: &mut &[u8]) -> Result<i64, ()> {
        let mut result = 0;
        let mut shift = 0;
        let size = 64;
        let mut byte;

        loop {
            byte = (*buf)[0];
            if shift == 63 && byte != 0x00 && byte != 0x7f {
                while buf[0] & CONTINUATION_BIT != 0 {
                    buf = &buf[1..];
                }
                return (Err(()), buf);
            }
            *buf = &(*buf)[1..];

            let low_bits = low_bits_of_byte(byte) as i64;
            result |= low_bits << shift;
            shift += 7;

            if byte & CONTINUATION_BIT == 0 {
                break;
            }
        }

        if shift < size && (SIGN_BIT & byte) == SIGN_BIT {
            // Sign extend the result.
            result |= !0 << shift;
        }

        Ok(result)
    }
}

/// A module for writing LEB128-encoded signed and unsigned integers.
pub mod write {
    use super::{low_bits_of_u64, CONTINUATION_BIT};
    use core::result::Result::{self, Ok};
    use core::marker::Sized;

    /// Write `val` to the buf as an unsigned LEB128 value.
    ///
    /// On success, return the number of bytes written to `w`.
    pub fn unsigned(buf: &mut &mut [u8], mut val: u64) -> usize {
        let mut bytes_written = 0;
        loop {
            let mut byte = low_bits_of_u64(val);
            val >>= 7;
            if val != 0 {
                // More bytes to come, so set the continuation bit.
                byte |= CONTINUATION_BIT;
            }

            (*buf)[0] = byte;
            *buf = &mut (*buf)[1..];
            bytes_written += 1;

            if val == 0 {
                return bytes_written;
            }
        }
    }

    /// Write `val` to the `buf` as a signed LEB128 value.
    ///
    /// On success, return the number of bytes written to `w`.
    pub fn signed(buf: &mut &mut [u8], mut val: i64) -> usize {
        let mut bytes_written = 0;
        loop {
            let mut byte = val as u8;
            // Keep the sign bit for testing
            val >>= 6;
            let done = val == 0 || val == -1;
            if done {
                byte &= !CONTINUATION_BIT;
            } else {
                // Remove the sign bit
                val >>= 1;
                // More bytes to come, so set the continuation bit.
                byte |= CONTINUATION_BIT;
            }

            (*buf)[0] = byte;
            *buf = &mut (*buf)[1..];
            bytes_written += 1;

            if done {
                return bytes_written;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_low_bits_of_byte() {
        for i in 0..127 {
            assert_eq!(i, low_bits_of_byte(i));
            assert_eq!(i, low_bits_of_byte(i | CONTINUATION_BIT));
        }
    }

    #[test]
    fn test_low_bits_of_u64() {
        for i in 0u64..127 {
            assert_eq!(i as u8, low_bits_of_u64(1 << 16 | i));
            assert_eq!(
                i as u8,
                low_bits_of_u64(i << 16 | i | (CONTINUATION_BIT as u64))
            );
        }
    }

    // Examples from the DWARF 4 standard, section 7.6, figure 22.
    #[test]
    fn test_read_unsigned() {
        let buf = [2u8];
        let mut readable = &buf[..];
        assert_eq!(
            2,
            read::unsigned(&mut readable).expect("Should read number")
        );

        let buf = [127u8];
        let mut readable = &buf[..];
        assert_eq!(
            127,
            read::unsigned(&mut readable).expect("Should read number")
        );

        let buf = [CONTINUATION_BIT, 1];
        let mut readable = &buf[..];
        assert_eq!(
            128,
            read::unsigned(&mut readable).expect("Should read number")
        );

        let buf = [1u8 | CONTINUATION_BIT, 1];
        let mut readable = &buf[..];
        assert_eq!(
            129,
            read::unsigned(&mut readable).expect("Should read number")
        );

        let buf = [2u8 | CONTINUATION_BIT, 1];
        let mut readable = &buf[..];
        assert_eq!(
            130,
            read::unsigned(&mut readable).expect("Should read number")
        );

        let buf = [57u8 | CONTINUATION_BIT, 100];
        let mut readable = &buf[..];
        assert_eq!(
            12857,
            read::unsigned(&mut readable).expect("Should read number")
        );
    }

    // Examples from the DWARF 4 standard, section 7.6, figure 23.
    #[test]
    fn test_read_signed() {
        let buf = [2u8];
        let mut readable = &buf[..];
        assert_eq!(2, read::signed(&mut readable).expect("Should read number"));

        let buf = [0x7eu8];
        let mut readable = &buf[..];
        assert_eq!(-2, read::signed(&mut readable).expect("Should read number"));

        let buf = [127u8 | CONTINUATION_BIT, 0];
        let mut readable = &buf[..];
        assert_eq!(
            127,
            read::signed(&mut readable).expect("Should read number")
        );

        let buf = [1u8 | CONTINUATION_BIT, 0x7f];
        let mut readable = &buf[..];
        assert_eq!(
            -127,
            read::signed(&mut readable).expect("Should read number")
        );

        let buf = [CONTINUATION_BIT, 1];
        let mut readable = &buf[..];
        assert_eq!(
            128,
            read::signed(&mut readable).expect("Should read number")
        );

        let buf = [CONTINUATION_BIT, 0x7f];
        let mut readable = &buf[..];
        assert_eq!(
            -128,
            read::signed(&mut readable).expect("Should read number")
        );

        let buf = [1u8 | CONTINUATION_BIT, 1];
        let mut readable = &buf[..];
        assert_eq!(
            129,
            read::signed(&mut readable).expect("Should read number")
        );

        let buf = [0x7fu8 | CONTINUATION_BIT, 0x7e];
        let mut readable = &buf[..];
        assert_eq!(
            -129,
            read::signed(&mut readable).expect("Should read number")
        );
    }

    #[test]
    fn test_read_signed_63_bits() {
        let buf = [
            CONTINUATION_BIT,
            CONTINUATION_BIT,
            CONTINUATION_BIT,
            CONTINUATION_BIT,
            CONTINUATION_BIT,
            CONTINUATION_BIT,
            CONTINUATION_BIT,
            CONTINUATION_BIT,
            0x40,
        ];
        let mut readable = &buf[..];
        assert_eq!(
            -0x4000000000000000,
            read::signed(&mut readable).expect("Should read number")
        );
    }

    #[test]
    #[should_panic]
    fn test_read_unsigned_not_enough_data() {
        let buf = [CONTINUATION_BIT];
        read::unsigned(&buf);
    }

    #[test]
    #[should_panic]
    fn test_read_signed_not_enough_data() {
        let buf = [CONTINUATION_BIT];
        read::signed(&buf);
    }

    #[test]
    #[should_panic]
    fn test_write_unsigned_not_enough_space() {
        let mut buf = [0; 1];
        write::unsigned(&mut buf, 128);
    }

    #[test]
    #[should_panic]
    fn test_write_signed_not_enough_space() {
        let mut buf = [0; 1];
        write::signed(&mut buf, 128);
    }

    #[test]
    fn dogfood_signed() {
        fn inner(i: i64) {
            let mut buf = [0u8; 1024];
            write::signed(&mut buf, i);
            let (result, _) = read::signed(&buf);
            assert_eq!(i, result);
        }
        for i in -513..513 {
            inner(i);
        }
        inner(core::i64::MIN);
    }

    #[test]
    fn dogfood_unsigned() {
        for i in 0..1025 {
            let mut buf = [0u8; 1024];
            write::unsigned(&mut buf, i);
            let result = read::unsigned(&buf);
            assert_eq!(i, result);
        }
    }

    #[test]
    fn test_read_unsigned_overflow() {
        let buf = [
            2u8 | CONTINUATION_BIT,
            2 | CONTINUATION_BIT,
            2 | CONTINUATION_BIT,
            2 | CONTINUATION_BIT,
            2 | CONTINUATION_BIT,
            2 | CONTINUATION_BIT,
            2 | CONTINUATION_BIT,
            2 | CONTINUATION_BIT,
            2 | CONTINUATION_BIT,
            2 | CONTINUATION_BIT,
            2 | CONTINUATION_BIT,
            2 | CONTINUATION_BIT,
            2 | CONTINUATION_BIT,
            2 | CONTINUATION_BIT,
            2 | CONTINUATION_BIT,
            2 | CONTINUATION_BIT,
            2 | CONTINUATION_BIT,
            2 | CONTINUATION_BIT,
            2 | CONTINUATION_BIT,
            2 | CONTINUATION_BIT,
            2 | CONTINUATION_BIT,
            2 | CONTINUATION_BIT,
            2 | CONTINUATION_BIT,
            2 | CONTINUATION_BIT,
            2 | CONTINUATION_BIT,
            2 | CONTINUATION_BIT,
            2 | CONTINUATION_BIT,
            2 | CONTINUATION_BIT,
            2 | CONTINUATION_BIT,
            2 | CONTINUATION_BIT,
            1,
        ];
        assert!(read::unsigned(&buf).0.is_err());
    }

    #[test]
    fn test_read_signed_overflow() {
        let buf = [
            2u8 | CONTINUATION_BIT,
            2 | CONTINUATION_BIT,
            2 | CONTINUATION_BIT,
            2 | CONTINUATION_BIT,
            2 | CONTINUATION_BIT,
            2 | CONTINUATION_BIT,
            2 | CONTINUATION_BIT,
            2 | CONTINUATION_BIT,
            2 | CONTINUATION_BIT,
            2 | CONTINUATION_BIT,
            2 | CONTINUATION_BIT,
            2 | CONTINUATION_BIT,
            2 | CONTINUATION_BIT,
            2 | CONTINUATION_BIT,
            2 | CONTINUATION_BIT,
            2 | CONTINUATION_BIT,
            2 | CONTINUATION_BIT,
            2 | CONTINUATION_BIT,
            2 | CONTINUATION_BIT,
            2 | CONTINUATION_BIT,
            2 | CONTINUATION_BIT,
            2 | CONTINUATION_BIT,
            2 | CONTINUATION_BIT,
            2 | CONTINUATION_BIT,
            2 | CONTINUATION_BIT,
            2 | CONTINUATION_BIT,
            2 | CONTINUATION_BIT,
            2 | CONTINUATION_BIT,
            2 | CONTINUATION_BIT,
            2 | CONTINUATION_BIT,
            1,
        ];
        assert!(read::signed(&buf).0.is_err());
    }

    #[test]
    fn test_read_multiple() {
        let buf = [2u8 | CONTINUATION_BIT, 1u8, 1u8];

        let mut readable = &buf[..];
        let mut result;
        (result, readable) = read::unsigned(&mut readable);
        assert_eq!(
            result.expect("Should read first number"),
            130u64
        );
        (result, readable) = read::unsigned(&mut readable);
        assert_eq!(
            result.expect("Should read first number"),
            1u64
        );
    }

    #[test]
    fn test_read_multiple_with_overflow() {
        let buf = [
            0b1111_1111,
            0b1111_1111,
            0b1111_1111,
            0b1111_1111,
            0b1111_1111,
            0b1111_1111,
            0b1111_1111,
            0b1111_1111,
            0b1111_1111,
            0b1111_1111,
            0b0111_1111, // Overflow!
            0b1110_0100,
            0b1110_0000,
            0b0000_0010, // 45156
        ];
        let mut readable = &buf[..];
        let mut result;
        
        (result, readable) = read::unsigned(&mut readable);
        assert!(result == Err(()));
        (result, readable) = read::unsigned(&mut readable);
        assert_eq!(
            result.expect("Should succeed with correct value"),
            45156
        );
    }
}
