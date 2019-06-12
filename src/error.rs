use ndarray;
use trackable::error::{ErrorKind as TrackableErrorKind, ErrorKindExt, Failure, TrackableError};

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

#[derive(Debug, Clone)]
pub enum ErrorKind {
    InvalidInput,
    InvalidFile,
    Unsupported,
    IoError,
    Other,
}
impl TrackableErrorKind for ErrorKind {}
