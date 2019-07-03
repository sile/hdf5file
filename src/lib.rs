//! An implementation of [HDF5 File Format].
//!
//! Note that this crate is in a very early stage of development and not intended to be used for production purposes.
//!
//! [HDF5 File Format]: https://support.hdfgroup.org/HDF5/doc/H5.format.html
#![warn(missing_docs)]

#[macro_use]
extern crate bitflags;
#[macro_use]
extern crate trackable;

pub use self::error::{Error, ErrorKind};
pub use self::file::Hdf5File;

mod error;
mod file;
mod io;
mod lowlevel;

/// This crate specific `Result` type.
pub type Result<T> = std::result::Result<T, Error>;
