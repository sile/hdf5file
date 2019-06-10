use crate::level0::Superblock;
use crate::Result;
use std::io::{Read, Seek};

#[derive(Debug)]
pub struct Hdf5File<T> {
    io: T,
    superblock: Superblock,
}
impl<T> Hdf5File<T>
where
    T: Read + Seek,
{
    pub fn new(mut io: T) -> Result<Self> {
        let superblock = track!(Superblock::from_reader(&mut io))?;
        Ok(Self { io, superblock })
    }
}
