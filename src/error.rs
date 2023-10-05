//! Scode Errors

use std::{error::Error, fmt::Display};

use crate::bindings;

/// SCode Error
///
/// This error occurs during parsing or dumping.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ScodeError {
    /// An error occurred while parsing
    Parse,
    /// An error occurred while dumping
    Dump,
    /// There are not enough bytes in the buffer
    Buffer,
    /// There was a CRC error while Parsing
    CRC,
    /// There was nothing to parse
    Empty,
    /// An unknown error occurred
    Unknown,
}

impl Error for ScodeError {}

impl Display for ScodeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            ScodeError::Parse => "Parse Error",
            ScodeError::Dump => "Dump Error",
            ScodeError::Buffer => "Buffer Error",
            ScodeError::CRC => "CRC Error",
            ScodeError::Empty => "Empty Error",
            ScodeError::Unknown => "Unknown Error",
        })
    }
}

impl From<i32> for ScodeError {
    fn from(value: i32) -> Self {
        match value {
            bindings::SCODE_ERROR_PARSE => Self::Parse,
            bindings::SCODE_ERROR_DUMP => Self::Dump,
            bindings::SCODE_ERROR_BUFFER => Self::Buffer,
            bindings::SCODE_ERROR_CRC => Self::CRC,
            bindings::SCODE_ERROR_EMPTY => Self::Empty,
            _ => Self::Unknown,
        }
    }
}

impl ScodeError {
    pub(crate) fn from_map<F, V>(val: i32, f: F) -> Result<V, Self>
    where
        F: FnOnce(u32) -> V,
    {
        if val < 0 {
            Err(val.into())
        } else {
            Ok(f(val as u32))
        }
    }

    /// Is the error a parse error
    pub fn is_parse(&self) -> bool {
        match self {
            ScodeError::Parse => true,
            _ => false,
        }
    }

    /// Is the error a dump error
    pub fn is_dump(&self) -> bool {
        match self {
            ScodeError::Dump => true,
            _ => false,
        }
    }

    /// Is the error a buffer error
    pub fn is_buffer(&self) -> bool {
        match self {
            ScodeError::Buffer => true,
            _ => false,
        }
    }

    /// Is the error a CRC error
    pub fn is_crc(&self) -> bool {
        match self {
            ScodeError::CRC => true,
            _ => false,
        }
    }

    /// Is the error an empty error
    pub fn is_empty(&self) -> bool {
        match self {
            ScodeError::Empty => true,
            _ => false,
        }
    }
}
