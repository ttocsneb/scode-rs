//! # SCode Wrapper
//!
//! SCode (Serial Code) is a language that is inspired by and backwards compatible
//! with GCode. It is intended to be a very light weight and efficient to parse language
//! for communicating between embedded devices. This library is designed to parse and
//! dump SCode.
//!
//! ## Serial Code Usage
//!
//! In this language specification, there is no explicit definitions for what each code
//! type is used for. It is however recommended to follow pre-existing standards (G-Codes
//! and M-Codes).
//!
//! Serial Codes can be used to issue commands or request information. A command would
//! work how one might expect it to where a serial code is sent and the receiver follows
//! the command. A request for information will look just like a command, but instead
//! of the receiver doing something, it will instead send a Serial Code back with the
//! requested information.
//!
//! Say you have a sensor 3 that is accessible through `S3`. You can request information
//! by sending the Serial Code `S3` and the receiver will send back something like
//! this: `S3 V123.4`.
//!
//! ## Language Specification
//!
//! There are two modes of communication: human and binary. These two modes both represent
//! the same data, but binary is designed to be more compact, easier to parse, and
//! more reliable. The human mode is fully compatible with GCode.
//!
//! A Serial Code starts with a code type: This is one of 26 letters (A-Z). Followed
//! by this type is a code number (0-255). After the code, any number of parameters
//! can be provided. A parameter is defined by a code and a value (also one of 26 letters).
//! The value can be a number or a string.
//!
//! You can determine whether a serial code is binary or human by the most significant
//! bit.
//!
//! ```txt
//! 0100 1101 - Start of human serial code
//! 1100 1101 - Start of binary serial code
//! ```
//!
//! ### Values
//!
//! In human form, there is really only two value types: number and string. The binary
//! values can be represented by one of 8 unit types: u8, i8, i16, i32, i64, f32, and
//! f64. The type of a value is encoded in the parameter code byte.
//!
//! The three most significant bits of a parameter code is reserved for the type.
//!
//! ```txt
//!        Code M = 0100 1101
//! Binary Code M = XXX0 1101
//! ```
//!
//! The coresponding types are as follows:
//!
//! * 000 = f64
//! * 001 = f32
//! * 010 = i64
//! * 011 = i32
//! * 100 = i16
//! * 101 = i8
//! * 110 = u8
//! * 111 = str
//!
//! After the binary parameter code, then the binary representation (in little endian)
//! follows. Strings are formatted as a null-terminated string.
//!
//! ### Binary Serial Codes
//!
//! The Binary serial code begins with the code type (the most significant bit is set
//! to 1). After this is the code number which is represented as a binary u8. After
//! this any number of parameters can be entered. The end of the parameters is marked
//! by a NULL character. After the parameters is a CRC-8 (poly: 0xD7) of the serial
//! code excluding the final NULL character and crc byte.
//!
//! Here is an example of a human code and it's binary alternative:
//!
//! ```txt
//! G34 X-2 Y3 Z4
//! 0xC7 0x22 0xB8 0xFE 0xB9 0x03 0xBA 0x04 0x00 0xB9
//! G    34   i8X  -2   i8Y  3    i8Z  4    end  crc
//! ```
//!
//! ## Language Definition
//!
//! There are two language definitions below. When parsing, only one or the other should
//! match. It is impossible for both languages to accept the same input string. When
//! parsing, any leading whitespace should be stripped.
//!
//! The first is the Human language definition. It is defined in terms of 8-bit ascii.
//!
//! ```txt
//! CODE ::= LETTER NUMERAL PADDING PARAMS COMMENT [\n] | COMMENT [\n]
//! PARAMS ::= PARAM PADDING | PARAMS | ε
//!
//! PADDING ::= SPACE PADDING | ε
//! SPACE ::= [ ] | [\t] | [\r]
//!
//! PARAM ::= LETTER STRING | LETTER NUMBER
//! LETTER ::= [A-Z] | [a-z]
//!
//! STRING ::= ["] CONTENTS_D ["] | ['] CONTENTS_S [']
//! CONTENTS_S ::= [^'] CONTENTS_S | ε
//! CONTENTS_D ::= [^"] CONTENTS_S | ε
//!
//! COMMENT ::= [;] CONTENTS_C | ε
//! CONTENTS_C ::= [^\n] CONTENTS_C | ε
//!
//! NUMBER ::= FLOAT | INTEGER
//! FLOAT ::= INTEGER [.] NUMERAL | [.] NUMERAL
//! INTEGER ::= [-] NUMERAL | NUMERAL
//! NUMERAL ::= DIGIT NUMERAL | DIGIT
//! DIGIT ::= [0-9]
//! ```
//!
//! The second is the Binary language definition and this is defined in terms of bits.
//!
//! ```txt
//! BCODE ::= [110] LETTER U8 PARAMS NULL U8
//!
//! PARAMS ::= PARAM_U8 PARAMS |
//!            PARAM_I8 PARAMS |
//!            PARAM_I16 PARAMS |
//!            PARAM_I32 PARAMS |
//!            PARAM_I64 PARAMS |
//!            PARAM_F32 PARAMS |
//!            PARAM_F64 PARAMS |
//!            PARAM_STR PARAMS | ε
//!
//! PARAM_U8  ::= [110] LETTER U8
//! PARAM_I8  ::= [101] LETTER I8
//! PARAM_I16 ::= [100] LETTER I16
//! PARAM_I32 ::= [011] LETTER I32
//! PARAM_I64 ::= [010] LETTER I64
//! PARAM_F32 ::= [001] LETTER F32
//! PARAM_F64 ::= [000] LETTER F64
//! PARAM_STR ::= [111] LETTER STR
//!
//! U8 ::= 8 * X
//! I8 ::= 8 * X
//! I16 ::= 16 * X
//! I32 ::= 32 * X
//! I64 ::= 64 * X
//! F32 ::= 32 * X
//! F64 ::= 64 * X
//! STR ::= U8 STR | NULL
//!
//! LETTER ::= [00001-11010]
//!
//! X ::= [0] | [1]
//! NULL ::= [00000000]
//! ```

use std::{
    borrow::Cow,
    ffi::{CStr, CString, NulError},
    fmt::{Debug, Display, Write},
    mem::{self, MaybeUninit},
    ops::{Index, IndexMut, Range},
    slice,
};

use std::str;

use std::os::raw::c_char;

use bindings::code_t;
use error::ScodeError;

use crate::bindings::param_t;

#[allow(non_camel_case_types, unused, non_upper_case_globals, non_snake_case)]
mod bindings;

pub mod error;

/// Parameter Value
#[derive(Debug, Clone, PartialEq)]
pub enum ParamValue {
    U8(u8),
    I8(i8),
    I16(i16),
    I32(i32),
    I64(i64),
    F32(f32),
    F64(f64),
    Str(Vec<u8>),
}

impl Display for ParamValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ParamValue::U8(v) => Display::fmt(v, f),
            ParamValue::I8(v) => Display::fmt(v, f),
            ParamValue::I16(v) => Display::fmt(v, f),
            ParamValue::I32(v) => Display::fmt(v, f),
            ParamValue::I64(v) => Display::fmt(v, f),
            ParamValue::F32(v) => Display::fmt(v, f),
            ParamValue::F64(v) => Display::fmt(v, f),
            ParamValue::Str(v) => {
                let q = v.contains(&b'\'');
                f.write_char(if q { '"' } else { '\'' })?;
                v.iter()
                    .map(|c| f.write_char(*c as char))
                    .collect::<Result<Vec<_>, _>>()?;
                f.write_char(if q { '"' } else { '\'' })
            }
        }
    }
}

impl From<u8> for ParamValue {
    fn from(value: u8) -> Self {
        Self::U8(value)
    }
}
impl From<i8> for ParamValue {
    fn from(value: i8) -> Self {
        Self::I8(value)
    }
}
impl From<i16> for ParamValue {
    fn from(value: i16) -> Self {
        Self::I16(value)
    }
}
impl From<i32> for ParamValue {
    fn from(value: i32) -> Self {
        Self::I32(value)
    }
}
impl From<i64> for ParamValue {
    fn from(value: i64) -> Self {
        Self::I64(value)
    }
}
impl From<f32> for ParamValue {
    fn from(value: f32) -> Self {
        Self::F32(value)
    }
}
impl From<f64> for ParamValue {
    fn from(value: f64) -> Self {
        Self::F64(value)
    }
}
impl<'a> From<&'a [u8]> for ParamValue {
    fn from(value: &'a [u8]) -> Self {
        Self::Str(value.into())
    }
}
impl From<Vec<u8>> for ParamValue {
    fn from(value: Vec<u8>) -> Self {
        Self::Str(value.into())
    }
}

macro_rules! cast {
    (cast_bytes, $t:ty, $s:ident, $str:expr, $num:expr) => {
        pub fn cast_bytes(self) -> $t {
            match self {
                Self::U8($s) => $num,
                Self::I8($s) => $num,
                Self::I16($s) => $num,
                Self::I32($s) => $num,
                Self::I64($s) => $num,
                Self::F32($s) => $num,
                Self::F64($s) => $num,
                Self::Str($s) => $str,
            }
        }
    };
    ($name:ident, $t:ty, $s:ty) => {
        pub fn $name(self) -> Result<$t, $s> {
            match self {
                Self::U8(v) => Ok(v as $t),
                Self::I8(v) => Ok(v as $t),
                Self::I16(v) => Ok(v as $t),
                Self::I32(v) => Ok(v as $t),
                Self::I64(v) => Ok(v as $t),
                Self::F32(v) => Ok(v as $t),
                Self::F64(v) => Ok(v as $t),
                Self::Str(v) => Err(v),
            }
        }
    };
}

impl ParamValue {
    pub fn str(val: impl Into<Vec<u8>>) -> Self {
        Self::Str(val.into())
    }

    cast!(cast_u8, u8, Vec<u8>);
    cast!(cast_i8, i8, Vec<u8>);
    cast!(cast_i16, i16, Vec<u8>);
    cast!(cast_i32, i32, Vec<u8>);
    cast!(cast_i64, i64, Vec<u8>);
    cast!(cast_f32, f32, Vec<u8>);
    cast!(cast_f64, f64, Vec<u8>);
    cast!(cast_bytes, Vec<u8>, v, v, v.to_string().into());

    pub fn as_borrowed(&self) -> ParamValueBorrowed {
        match self {
            ParamValue::U8(v) => ParamValueBorrowed::U8(*v),
            ParamValue::I8(v) => ParamValueBorrowed::I8(*v),
            ParamValue::I16(v) => ParamValueBorrowed::I16(*v),
            ParamValue::I32(v) => ParamValueBorrowed::I32(*v),
            ParamValue::I64(v) => ParamValueBorrowed::I64(*v),
            ParamValue::F32(v) => ParamValueBorrowed::F32(*v),
            ParamValue::F64(v) => ParamValueBorrowed::F64(*v),
            ParamValue::Str(v) => ParamValueBorrowed::Str(v.as_ref()),
        }
    }
}

/// Borrowed Parameter Value
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ParamValueBorrowed<'a> {
    U8(u8),
    I8(i8),
    I16(i16),
    I32(i32),
    I64(i64),
    F32(f32),
    F64(f64),
    Str(&'a [u8]),
}

impl<'a> From<u8> for ParamValueBorrowed<'a> {
    fn from(value: u8) -> Self {
        Self::U8(value)
    }
}
impl<'a> From<i8> for ParamValueBorrowed<'a> {
    fn from(value: i8) -> Self {
        Self::I8(value)
    }
}
impl<'a> From<i16> for ParamValueBorrowed<'a> {
    fn from(value: i16) -> Self {
        Self::I16(value)
    }
}
impl<'a> From<i32> for ParamValueBorrowed<'a> {
    fn from(value: i32) -> Self {
        Self::I32(value)
    }
}
impl<'a> From<i64> for ParamValueBorrowed<'a> {
    fn from(value: i64) -> Self {
        Self::I64(value)
    }
}
impl<'a> From<f32> for ParamValueBorrowed<'a> {
    fn from(value: f32) -> Self {
        Self::F32(value)
    }
}
impl<'a> From<f64> for ParamValueBorrowed<'a> {
    fn from(value: f64) -> Self {
        Self::F64(value)
    }
}
impl<'a> From<&'a [u8]> for ParamValueBorrowed<'a> {
    fn from(value: &'a [u8]) -> Self {
        Self::Str(value)
    }
}

impl<'a> From<ParamValueBorrowed<'a>> for ParamValue {
    fn from(value: ParamValueBorrowed<'a>) -> Self {
        match value {
            ParamValueBorrowed::U8(v) => ParamValue::U8(v),
            ParamValueBorrowed::I8(v) => ParamValue::I8(v),
            ParamValueBorrowed::I16(v) => ParamValue::I16(v),
            ParamValueBorrowed::I32(v) => ParamValue::I32(v),
            ParamValueBorrowed::I64(v) => ParamValue::I64(v),
            ParamValueBorrowed::F32(v) => ParamValue::F32(v),
            ParamValueBorrowed::F64(v) => ParamValue::F64(v),
            ParamValueBorrowed::Str(v) => ParamValue::Str(v.into()),
        }
    }
}

impl<'a> ParamValueBorrowed<'a> {
    cast!(cast_u8, u8, &'a [u8]);
    cast!(cast_i8, i8, &'a [u8]);
    cast!(cast_i16, i16, &'a [u8]);
    cast!(cast_i32, i32, &'a [u8]);
    cast!(cast_i64, i64, &'a [u8]);
    cast!(cast_f32, f32, &'a [u8]);
    cast!(cast_f64, f64, &'a [u8]);
    cast!(
        cast_bytes,
        Cow<'a, [u8]>,
        v,
        Cow::Borrowed(v),
        Cow::Owned(v.to_string().into())
    );
}

#[derive(Debug, Clone, PartialEq)]
pub struct ParamSend {
    pub letter: u8,
    pub value: ParamValue,
}

impl Display for ParamSend {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{}{}", self.letter as char, self.value))
    }
}

impl From<Param> for ParamSend {
    fn from(value: Param) -> Self {
        Self {
            letter: value.letter(),
            value: value.into(),
        }
    }
}

impl TryFrom<ParamSend> for Param {
    type Error = NulError;

    fn try_from(value: ParamSend) -> Result<Self, Self::Error> {
        Self::new(value.letter, value.value)
    }
}

#[inline]
fn dump_vec<F>(f: F) -> Result<Vec<u8>, ScodeError>
where
    F: Fn(&mut [u8]) -> Result<usize, ScodeError>,
{
    let mut buf = vec![0; 16];
    loop {
        match f(buf.as_mut_slice()) {
            Ok(len) => return Ok(Vec::from(&buf[0..len])),
            Err(ScodeError::Buffer) => {
                buf = vec![0; buf.len() * 2];
            }
            Err(err) => return Err(err),
        }
    }
}

/// Parameter
///
/// A parameter has a letter and a value.
pub struct Param(bindings::param_t);

impl Debug for Param {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let letter = self.letter();
        let value = self.value();

        f.write_fmt(format_args!(
            "Param {{ letter: {letter:?} value: {value:?} }}"
        ))
    }
}

impl Default for Param {
    fn default() -> Self {
        Param(unsafe { bindings::init_param_u8(0, 0) })
    }
}

impl Display for Param {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.dump_human_vec() {
            Ok(buf) => match str::from_utf8(&buf) {
                Ok(buf) => f.write_fmt(format_args!("{buf}")),
                Err(_) => f.write_fmt(format_args!("{buf:?}")),
            },
            Err(_) => f.write_str("Invalid Param"),
        }
    }
}

impl Param {
    /// Create a u8 parameter
    pub fn new_u8(letter: u8, val: u8) -> Self {
        Param(unsafe { bindings::init_param_u8(letter as c_char, val) })
    }
    /// Create a i8 parameter
    pub fn new_i8(letter: u8, val: i8) -> Self {
        Param(unsafe { bindings::init_param_i8(letter as c_char, val) })
    }
    /// Create a i16 parameter
    pub fn new_i16(letter: u8, val: i16) -> Self {
        Param(unsafe { bindings::init_param_i16(letter as c_char, val) })
    }
    /// Create a i32 parameter
    pub fn new_i32(letter: u8, val: i32) -> Self {
        Param(unsafe { bindings::init_param_i32(letter as c_char, val) })
    }
    /// Create a i64 parameter
    pub fn new_i64(letter: u8, val: i64) -> Self {
        Param(unsafe { bindings::init_param_i64(letter as c_char, val) })
    }
    /// Create a f32 parameter
    pub fn new_f32(letter: u8, val: f32) -> Self {
        Param(unsafe { bindings::init_param_f32(letter as c_char, val) })
    }
    /// Create a f64 parameter
    pub fn new_f64(letter: u8, val: f64) -> Self {
        Param(unsafe { bindings::init_param_f64(letter as c_char, val) })
    }
    /// Create a str parameter
    pub fn new_str(letter: u8, val: impl Into<Vec<u8>>) -> Result<Self, NulError> {
        let val = CString::new(val)?;
        Ok(Param(unsafe {
            bindings::init_param_str(letter as c_char, val.as_ptr())
        }))
    }
    pub fn new(letter: u8, val: impl Into<ParamValue>) -> Result<Self, NulError> {
        match val.into() {
            ParamValue::U8(val) => Ok(Self::new_u8(letter, val)),
            ParamValue::I8(val) => Ok(Self::new_i8(letter, val)),
            ParamValue::I16(val) => Ok(Self::new_i16(letter, val)),
            ParamValue::I32(val) => Ok(Self::new_i32(letter, val)),
            ParamValue::I64(val) => Ok(Self::new_i64(letter, val)),
            ParamValue::F32(val) => Ok(Self::new_f32(letter, val)),
            ParamValue::F64(val) => Ok(Self::new_f64(letter, val)),
            ParamValue::Str(val) => Self::new_str(letter, val),
        }
    }

    /// Cast the value into a u8
    ///
    /// The value will be converted into a u8 or None if it is a str
    pub fn cast_u8(&self) -> Option<u8> {
        if self.typ() == bindings::PARAM_T_STR {
            None
        } else {
            Some(unsafe { bindings::param_cast_u8(&self.0) })
        }
    }
    /// Cast the value into a i8
    ///
    /// The value will be converted into a i8 or None if it is a str
    pub fn cast_i8(&self) -> Option<i8> {
        if self.typ() == bindings::PARAM_T_STR {
            None
        } else {
            Some(unsafe { bindings::param_cast_i8(&self.0) })
        }
    }
    /// Cast the value into a i16
    ///
    /// The value will be converted into a i16 or None if it is a str
    pub fn cast_i16(&self) -> Option<i16> {
        if self.typ() == bindings::PARAM_T_STR {
            None
        } else {
            Some(unsafe { bindings::param_cast_i16(&self.0) })
        }
    }
    /// Cast the value into a i32
    ///
    /// The value will be converted into a i32 or None if it is a str
    pub fn cast_i32(&self) -> Option<i32> {
        if self.typ() == bindings::PARAM_T_STR {
            None
        } else {
            Some(unsafe { bindings::param_cast_i32(&self.0) })
        }
    }
    /// Cast the value into a i64
    ///
    /// The value will be converted into a i64 or None if it is a str
    pub fn cast_i64(&self) -> Option<i64> {
        if self.typ() == bindings::PARAM_T_STR {
            None
        } else {
            Some(unsafe { bindings::param_cast_i64(&self.0) })
        }
    }
    /// Cast the value into a f32
    ///
    /// The value will be converted into a f32 or None if it is a str
    pub fn cast_f32(&self) -> Option<f32> {
        if self.typ() == bindings::PARAM_T_STR {
            None
        } else {
            Some(unsafe { bindings::param_cast_f32(&self.0) })
        }
    }
    /// Cast the value into a f64
    ///
    /// The value will be converted into a f64 or None if it is a str
    pub fn cast_f64(&self) -> Option<f64> {
        if self.typ() == bindings::PARAM_T_STR {
            None
        } else {
            Some(unsafe { bindings::param_cast_f64(&self.0) })
        }
    }
    /// Cast the value into a str
    ///
    /// The value will be converted into a str or None if it is a number
    pub fn cast_str(&self) -> Option<&[u8]> {
        if self.typ() == bindings::PARAM_T_STR {
            Some(unsafe { CStr::from_ptr(self.0.__bindgen_anon_1.str_) }.to_bytes())
        } else {
            None
        }
    }

    /// Check if the value is a str
    pub fn is_str(&self) -> bool {
        self.typ() == bindings::PARAM_T_STR
    }

    /// Check if the value is a num
    pub fn is_num(&self) -> bool {
        self.typ() != bindings::PARAM_T_STR
    }

    /// Get the letter of the param
    #[inline]
    pub fn letter(&self) -> u8 {
        (unsafe { bindings::param_letter(&self.0) } as u8)
    }

    /// Get the value of the param
    pub fn value(&self) -> ParamValueBorrowed {
        match self.typ() {
            bindings::PARAM_T_U8 => unsafe { self.0.__bindgen_anon_1.u8_ }.into(),
            bindings::PARAM_T_I8 => unsafe { self.0.__bindgen_anon_1.i8_ }.into(),
            bindings::PARAM_T_I16 => unsafe { self.0.__bindgen_anon_1.i16_ }.into(),
            bindings::PARAM_T_I32 => unsafe { self.0.__bindgen_anon_1.i32_ }.into(),
            bindings::PARAM_T_F32 => unsafe { self.0.__bindgen_anon_1.f32_ }.into(),
            bindings::PARAM_T_F64 => unsafe { self.0.__bindgen_anon_1.f64_ }.into(),
            bindings::PARAM_T_STR => unsafe { CStr::from_ptr(self.0.__bindgen_anon_1.str_) }
                .to_bytes()
                .into(),
            bindings::PARAM_T_I64 | _ => unsafe { self.0.__bindgen_anon_1.i64_ }.into(),
        }
    }

    fn typ(&self) -> u32 {
        (unsafe { bindings::param_type(&self.0) } as u32)
    }

    fn into_param_t(self) -> bindings::param_t {
        let param = bindings::param_t {
            __bindgen_anon_1: self.0.__bindgen_anon_1,
            param: self.0.param,
        };
        mem::forget(self);
        param
    }

    /// Parse a human param
    ///
    /// This will parse the next param and return the unparsed buffer
    pub fn parse_human(buf: &[u8]) -> Result<(Self, &[u8]), ScodeError> {
        let mut param: MaybeUninit<param_t> = MaybeUninit::uninit();
        let read = unsafe {
            bindings::param_parse_human(
                param.as_mut_ptr(),
                buf.as_ptr() as *const c_char,
                buf.len(),
            )
        };
        ScodeError::from_map(read, |read| {
            (Param(unsafe { param.assume_init() }), &buf[read as usize..])
        })
    }

    /// Parse a binary param
    ///
    /// This will parse the next param and return the unparsed buffer
    pub fn parse_binary(buf: &[u8]) -> Result<(Self, &[u8]), ScodeError> {
        let mut param: MaybeUninit<param_t> = MaybeUninit::uninit();
        let read = unsafe {
            bindings::param_parse_binary(
                param.as_mut_ptr(),
                buf.as_ptr() as *const c_char,
                buf.len(),
            )
        };
        ScodeError::from_map(read, |read| {
            (Param(unsafe { param.assume_init() }), &buf[read as usize..])
        })
    }

    /// Dump the param into the buffer in binary format
    pub fn dump_binary(&self, buf: &mut [u8]) -> Result<usize, ScodeError> {
        let written = unsafe {
            bindings::param_dump_binary(&self.0, buf.as_mut_ptr() as *mut c_char, buf.len())
        };

        ScodeError::from_map(written, move |written| written as usize)
    }

    /// Dump the param into the buffer in human format
    pub fn dump_human(&self, buf: &mut [u8]) -> Result<usize, ScodeError> {
        let written = unsafe {
            bindings::param_dump_human(&self.0, buf.as_mut_ptr() as *mut c_char, buf.len())
        };

        ScodeError::from_map(written, move |written| written as usize)
    }

    pub fn dump_human_vec(&self) -> Result<Vec<u8>, ScodeError> {
        dump_vec(|b| self.dump_human(b))
    }

    pub fn dump_binary_vec(&self) -> Result<Vec<u8>, ScodeError> {
        dump_vec(|b| self.dump_binary(b))
    }
}

impl Drop for Param {
    fn drop(&mut self) {
        unsafe {
            bindings::free_param(&mut self.0);
        }
    }
}

impl From<Param> for ParamValue {
    fn from(value: Param) -> Self {
        match value.typ() {
            bindings::PARAM_T_U8 => unsafe { value.0.__bindgen_anon_1.u8_ }.into(),
            bindings::PARAM_T_I8 => unsafe { value.0.__bindgen_anon_1.i8_ }.into(),
            bindings::PARAM_T_I16 => unsafe { value.0.__bindgen_anon_1.i16_ }.into(),
            bindings::PARAM_T_I32 => unsafe { value.0.__bindgen_anon_1.i32_ }.into(),
            bindings::PARAM_T_F32 => unsafe { value.0.__bindgen_anon_1.f32_ }.into(),
            bindings::PARAM_T_F64 => unsafe { value.0.__bindgen_anon_1.f64_ }.into(),
            bindings::PARAM_T_STR => unsafe { CStr::from_ptr(value.0.__bindgen_anon_1.str_) }
                .to_bytes()
                .into(),
            bindings::PARAM_T_I64 | _ => unsafe { value.0.__bindgen_anon_1.i64_ }.into(),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct CodeSend {
    pub letter: u8,
    pub number: u8,
    pub params: Vec<ParamSend>,
}

impl Display for CodeSend {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{}{}", self.letter as char, self.number))?;
        for param in &self.params {
            f.write_fmt(format_args!(" {param}"))?;
        }
        Ok(())
    }
}

impl From<Code> for CodeSend {
    fn from(value: Code) -> Self {
        Self {
            letter: value.letter(),
            number: value.number(),
            params: value.into_iter().map(|v| v.into()).collect(),
        }
    }
}

impl TryFrom<CodeSend> for Code {
    type Error = NulError;

    fn try_from(value: CodeSend) -> Result<Self, Self::Error> {
        Ok(Self::new_params(
            value.letter,
            value.number,
            value
                .params
                .into_iter()
                .map(|v| v.clone().try_into())
                .collect::<Result<Vec<_>, _>>()?,
        ))
    }
}

impl CodeSend {
    pub fn find(&self, letter: u8) -> Option<&ParamSend> {
        self.params.iter().filter(|p| p.letter == letter).next()
    }

    pub fn find_mut(&mut self, letter: u8) -> Option<&mut ParamSend> {
        self.params.iter_mut().filter(|p| p.letter == letter).next()
    }
}

/// SCode
///
/// The code consists of a letter, number and a series of params.
pub struct Code {
    code: bindings::code_t,
    len: usize,
}

impl Debug for Code {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let letter = self.letter();
        let number = self.number();
        let params = self.params();
        f.write_fmt(format_args!(
            "Code {{ letter: {letter:?}, number: {number:?}, params: {params:?} }}"
        ))
    }
}

impl Display for Code {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.dump_human_vec() {
            Ok(buf) => {
                let buf = &buf[0..buf.len() - 1];
                match str::from_utf8(&buf) {
                    Ok(buf) => f.write_fmt(format_args!("{buf}")),
                    Err(_) => f.write_fmt(format_args!("{buf:?}")),
                }
            }
            Err(_) => f.write_str("Invalid Param"),
        }
    }
}

impl From<code_t> for Code {
    fn from(value: code_t) -> Self {
        let mut len = 0;
        if !value.params.is_null() {
            while (unsafe { &*value.params.add(len) }).param != 0 {
                len += 1;
            }
        }
        Code { code: value, len }
    }
}

impl Code {
    /// Create a new code
    pub fn new_params<I>(letter: u8, number: u8, params: I) -> Self
    where
        I: IntoIterator<Item = Param>,
    {
        let params = params.into_iter();
        let len = match params.size_hint().1 {
            Some(len) => len,
            None => return Self::new_params(letter, number, params.collect::<Vec<_>>()),
        };
        let code = unsafe { bindings::init_code(letter as c_char, number, len) };

        let param_arr = unsafe { slice::from_raw_parts_mut(code.params, len) };

        for (src, dst) in params.zip(param_arr) {
            mem::forget(mem::replace(dst, src.into_param_t()));
        }

        Self { code, len }
    }

    pub fn new(letter: u8, number: u8) -> Self {
        let code = unsafe { bindings::init_code(letter as c_char, number, 0) };

        Self { code, len: 0 }
    }

    /// Get the number of params in the code
    #[inline]
    pub fn len(&self) -> usize {
        self.len
    }

    /// Get the code letter
    #[inline]
    pub fn letter(&self) -> u8 {
        (unsafe { bindings::code_letter(&self.code) } as u8)
    }

    /// Get the code number
    #[inline]
    pub fn number(&self) -> u8 {
        self.code.number
    }

    /// Was the parsed code binary
    ///
    /// This function is only useful when the code was parsed
    #[inline]
    pub fn is_binary(&self) -> bool {
        (unsafe { bindings::code_is_binary(&self.code) } != 0)
    }

    /// Get the params
    #[inline]
    pub fn params(&self) -> &[Param] {
        unsafe {
            slice::from_raw_parts(self.code.params as *const param_t as *const Param, self.len)
        }
    }

    /// Get the params as mut
    #[inline]
    pub fn params_mut(&mut self) -> &mut [Param] {
        unsafe { slice::from_raw_parts_mut(self.code.params as *mut Param, self.len) }
    }

    /// Get an iterator over the params
    #[inline]
    pub fn iter(&self) -> CodeIter<&Self> {
        self.into_iter()
    }

    /// Get an mutable iterator over the params
    #[inline]
    pub fn iter_mut(&mut self) -> CodeIter<&mut Self> {
        self.into_iter()
    }

    /// Parse a code
    ///
    /// returns the parsed code as well as any unparsed buffer
    pub fn parse(buf: &[u8]) -> Result<(Self, &[u8]), ScodeError> {
        let mut code: MaybeUninit<bindings::code_t> = MaybeUninit::uninit();
        let read = unsafe {
            bindings::code_parse(code.as_mut_ptr(), buf.as_ptr() as *const c_char, buf.len())
        };
        ScodeError::from_map(read, |read| {
            let code = unsafe { code.assume_init() };
            (code.into(), &buf[read as usize..])
        })
    }

    /// dump the code into a binary format
    pub fn dump_binary(&self, buf: &mut [u8]) -> Result<usize, ScodeError> {
        let written = unsafe {
            bindings::code_dump_binary(&self.code, buf.as_mut_ptr() as *mut c_char, buf.len())
        };

        ScodeError::from_map(written, |written| written as usize)
    }

    /// dump the code into a human format
    pub fn dump_human(&self, buf: &mut [u8]) -> Result<usize, ScodeError> {
        let written = unsafe {
            bindings::code_dump_human(&self.code, buf.as_mut_ptr() as *mut c_char, buf.len())
        };

        ScodeError::from_map(written, |written| written as usize)
    }

    pub fn dump_human_vec(&self) -> Result<Vec<u8>, ScodeError> {
        dump_vec(|b| self.dump_human(b))
    }

    pub fn dump_binary_vec(&self) -> Result<Vec<u8>, ScodeError> {
        dump_vec(|b| self.dump_binary(b))
    }
}

impl Index<usize> for Code {
    type Output = Param;

    fn index(&self, index: usize) -> &Self::Output {
        &self.params()[index]
    }
}

impl IndexMut<usize> for Code {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.params_mut()[index]
    }
}

impl Index<Range<usize>> for Code {
    type Output = [Param];

    fn index(&self, index: Range<usize>) -> &Self::Output {
        &self.params()[index]
    }
}

impl IndexMut<Range<usize>> for Code {
    fn index_mut(&mut self, index: Range<usize>) -> &mut Self::Output {
        &mut self.params_mut()[index]
    }
}

pub struct CodeIter<T> {
    code: T,
    start: usize,
    end: usize,
}

impl<'a, T> ExactSizeIterator for CodeIter<T>
where
    CodeIter<T>: Iterator,
{
    fn len(&self) -> usize {
        self.start - self.end
    }
}

impl<'a> Iterator for CodeIter<&'a Code> {
    type Item = &'a Param;

    fn next(&mut self) -> Option<Self::Item> {
        if self.start >= self.code.len() {
            None
        } else {
            let val = &self.code[self.start];
            self.start += 1;
            Some(val)
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.code.len(), Some(self.code.len()))
    }
}

impl<'a> DoubleEndedIterator for CodeIter<&'a Code> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.start >= self.end {
            None
        } else {
            self.end -= 1;
            Some(&self.code[self.end])
        }
    }
}

impl<'a> IntoIterator for &'a Code {
    type Item = &'a Param;

    type IntoIter = CodeIter<&'a Code>;

    fn into_iter(self) -> Self::IntoIter {
        CodeIter {
            code: self,
            start: 0,
            end: self.len,
        }
    }
}

impl<'a> Iterator for CodeIter<&'a mut Code> {
    type Item = &'a mut Param;

    fn next(&mut self) -> Option<Self::Item> {
        if self.start >= self.end {
            None
        } else {
            let params_arr =
                unsafe { slice::from_raw_parts_mut(self.code.code.params, self.code.len) };
            let p_ptr = &mut params_arr[self.start];
            let p_ref = unsafe { &mut *(p_ptr as *mut param_t as *mut Param) };
            self.start += 1;
            Some(p_ref)
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.code.len(), Some(self.code.len()))
    }
}

impl<'a> DoubleEndedIterator for CodeIter<&'a mut Code> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.start >= self.end {
            None
        } else {
            self.end -= 1;
            let params_arr =
                unsafe { slice::from_raw_parts_mut(self.code.code.params, self.code.len) };
            let p_ptr = &mut params_arr[self.end];
            let p_ref = unsafe { &mut *(p_ptr as *mut param_t as *mut Param) };
            Some(p_ref)
        }
    }
}

impl<'a> IntoIterator for &'a mut Code {
    type Item = &'a mut Param;

    type IntoIter = CodeIter<&'a mut Code>;

    fn into_iter(self) -> Self::IntoIter {
        let end = self.len;
        CodeIter {
            code: self,
            start: 0,
            end,
        }
    }
}

impl Iterator for CodeIter<Code> {
    type Item = Param;

    fn next(&mut self) -> Option<Self::Item> {
        if self.start >= self.code.len() {
            None
        } else {
            let val = mem::take(&mut self.code[self.start]);
            self.start += 1;
            Some(val)
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.code.len(), Some(self.code.len()))
    }
}

impl DoubleEndedIterator for CodeIter<Code> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.start >= self.end {
            None
        } else {
            self.end -= 1;
            Some(mem::take(&mut self.code[self.end]))
        }
    }
}

impl IntoIterator for Code {
    type Item = Param;

    type IntoIter = CodeIter<Code>;

    fn into_iter(self) -> Self::IntoIter {
        let end = self.len;
        CodeIter {
            code: self,
            start: 0,
            end,
        }
    }
}

impl Drop for Code {
    fn drop(&mut self) {
        unsafe { bindings::free_code(&mut self.code) }
    }
}

/// Stream Parser
pub struct CodeStream(bindings::code_stream_t);

impl Drop for CodeStream {
    fn drop(&mut self) {
        unsafe { bindings::free_code_stream(&mut self.0) }
    }
}

impl Iterator for CodeStream {
    type Item = Result<Code, ScodeError>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.pop() {
            Ok(Some(code)) => Some(Ok(code)),
            Ok(None) => None,
            Err(err) => Some(Err(err)),
        }
    }
}

impl CodeStream {
    /// Create a new CodeStream with a starting buffer size
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        Self(unsafe { bindings::init_code_stream(capacity) })
    }

    /// Create a new CodeStream
    #[inline]
    pub fn new() -> Self {
        Self::with_capacity(0)
    }

    /// Push a byte into the stream
    #[inline]
    pub fn push(&mut self, v: u8) {
        unsafe { bindings::code_stream_update(&mut self.0, &(v as c_char), 1) };
    }

    /// Push a byte string into the stream
    #[inline]
    pub fn extend(&mut self, val: impl AsRef<[u8]>) {
        let val = val.as_ref();
        unsafe {
            bindings::code_stream_update(&mut self.0, val.as_ptr() as *const c_char, val.len())
        }
    }

    /// Push an iterable into the stream
    pub fn push_all<I>(&mut self, i: I)
    where
        I: IntoIterator<Item = u8>,
    {
        for val in i {
            self.push(val);
        }
    }

    /// Pop the next code out of the stream
    pub fn pop(&mut self) -> Result<Option<Code>, ScodeError> {
        let mut code: MaybeUninit<code_t> = MaybeUninit::uninit();
        let res = unsafe { bindings::code_stream_pop(&mut self.0, code.as_mut_ptr()) };

        if res != 0 {
            if res == bindings::SCODE_ERROR_BUFFER {
                Ok(None)
            } else {
                Err(res.into())
            }
        } else {
            Ok(Some(unsafe { code.assume_init() }.into()))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_param() {
        let param = Param::new_u8(b'a', 5);

        assert_eq!(param.value(), ParamValueBorrowed::U8(5));
        assert_eq!(param.letter(), b'A');
    }

    #[test]
    fn test_param_str() {
        let param = Param::new_str(b'Z', "hello").unwrap();

        assert_eq!(param.value(), ParamValueBorrowed::Str(b"hello"));
        assert_eq!(param.letter(), b'Z');
    }

    #[test]
    fn test_code() {
        let params = [
            Param::new_u8(b'a', 3),
            Param::new_i32(b'b', 1234),
            Param::new_str(b'c', "Hello World!").unwrap(),
        ];

        let code = Code::new_params(b'c', 12, params.into_iter());

        assert_eq!(code.len(), 3);
        assert_eq!(code.letter(), b'C');
        assert_eq!(code.number(), 12);

        let mut iter = code.into_iter();
        assert_eq!(iter.next().unwrap().value(), ParamValueBorrowed::U8(3));
        assert_eq!(iter.next().unwrap().value(), ParamValueBorrowed::I32(1234));
        assert_eq!(
            iter.next().unwrap().value(),
            ParamValueBorrowed::Str(b"Hello World!")
        );
    }

    #[test]
    fn test_param_parse() {
        let param = Param::parse_human(b"g3 x0 y-1 z2").unwrap();
        assert_eq!(param.0.letter(), b'G');
        assert_eq!(param.0.value(), ParamValueBorrowed::U8(3));
        assert_eq!(param.1, b" x0 y-1 z2");
    }

    #[test]
    fn test_code_parse() {
        let code = Code::parse(b"g3 x0 y-1 z2\n").unwrap();
        assert_eq!(code.1, b"");
        assert_eq!(code.0.letter(), b'G');
        assert_eq!(code.0.number(), 3);

        let mut iter = code.0.into_iter();

        let param = iter.next().unwrap();
        assert_eq!(param.letter(), b'X');
        assert_eq!(param.value(), ParamValueBorrowed::U8(0));

        let param = iter.next().unwrap();
        assert_eq!(param.letter(), b'Y');
        assert_eq!(param.value(), ParamValueBorrowed::I8(-1));

        let param = iter.next().unwrap();
        assert_eq!(param.letter(), b'Z');
        assert_eq!(param.value(), ParamValueBorrowed::U8(2));

        assert!(iter.next().is_none());
    }

    #[test]
    fn test_code_stream() {
        let mut cs = CodeStream::with_capacity(64);
        cs.extend(
            "; Move the head to 4,5,3
             G1 X4 Y5 Z3
             ",
        );

        let cmd = cs.pop().unwrap();
        assert_eq!(cmd.letter(), b'G');
        assert_eq!(cmd.number(), 1);
        let mut iter = cmd.into_iter();

        let param = iter.next().unwrap();
        assert_eq!(param.letter(), b'X');
        assert_eq!(param.cast_f32().unwrap(), 4.0);

        let param = iter.next().unwrap();
        assert_eq!(param.letter(), b'Y');
        assert_eq!(param.cast_f32().unwrap(), 5.0);

        let param = iter.next().unwrap();
        assert_eq!(param.letter(), b'Z');
        assert_eq!(param.cast_f32().unwrap(), 3.0);

        assert!(iter.next().is_none());

        let err = cs.pop().unwrap_err();
        assert!(err.is_buffer());
    }
}
