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

#[derive(Debug, Clone)]
pub enum ErrorKind {
    InvalidFile,
    Unsupported,
    IoError,
    Other,
}
impl TrackableErrorKind for ErrorKind {}
