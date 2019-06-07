/// https://support.hdfgroup.org/HDF5/doc/H5.format.html
#[macro_use]
extern crate bitflags;
#[macro_use]
extern crate trackable;

pub use self::error::{Error, ErrorKind};

pub mod level0;

mod error;
mod io;

pub type Result<T> = std::result::Result<T, Error>;
