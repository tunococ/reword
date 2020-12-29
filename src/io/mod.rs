//! Contains tools for handling input and output.
//! 
//! Using [`reword`] generally does not require
//!     the user to know about anything inside this module (`reword::io`),
//!     but they are provided here in case anyone finds them useful,
//!     or wants to help expand [`reword`].
//! Navigate to submodules of `reword::io` to see more documentation.
//! 
//! [`reword`]: crate

pub mod utf8;

pub use self::utf8::*;

