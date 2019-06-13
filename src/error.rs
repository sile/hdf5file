use ndarray;
use trackable::error::{
    ErrorKind as TrackableErrorKind, ErrorKindExt, Failed, Failure, TrackableError,
};

/// This crate specific `Error` type.
#[derive(Debug, Clone, TrackableError)]
pub struct Error(TrackableError<ErrorKind>);
impl From<Failure> for Error {
    fn from(f: Failure) -> Self {
        ErrorKind::Other.takes_over(f).into()
    }
}
impl From<std::io::Error> for Error {
    fn from(f: std::io::Error) -> Self {
        ErrorKind::IoError.cause(f).into()
    }
}
impl From<std::string::FromUtf8Error> for Error {
    fn from(f: std::string::FromUtf8Error) -> Self {
        ErrorKind::InvalidFile.cause(f).into()
    }
}
impl From<ndarray::ShapeError> for Error {
    fn from(f: ndarray::ShapeError) -> Self {
        ErrorKind::InvalidInput.cause(f).into()
    }
}
impl From<Error> for Failure {
    fn from(f: Error) -> Self {
        Failed.takes_over(f).into()
    }
}

/// Possible error kinds.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ErrorKind {
    /// Input is invalid.
    InvalidInput,

    /// Wrong HDF5 file.
    InvalidFile,

    /// Unsupported feature.
    Unsupported,

    /// I/O error.
    IoError,

    /// Other erorr.
    Other,
}
impl TrackableErrorKind for ErrorKind {}
