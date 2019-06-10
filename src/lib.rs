/// https://support.hdfgroup.org/HDF5/doc/H5.format.html
#[macro_use]
extern crate bitflags;
#[macro_use]
extern crate trackable;

pub use self::error::{Error, ErrorKind};
pub use self::file::Hdf5File;
pub use self::object::Object;

pub mod level0;
pub mod level1;

mod error;
mod file;
mod io;
mod object;

pub type Result<T> = std::result::Result<T, Error>;
