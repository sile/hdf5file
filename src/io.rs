use crate::{Error, Result};
use byteorder::{LittleEndian, ReadBytesExt};
use std::io::Read;

pub trait ReadExt: Read {
    fn read_bytes(&mut self, buf: &mut [u8]) -> Result<()> {
        track!(self.read_exact(buf).map_err(Error::from))
    }

    fn read_u8(&mut self) -> Result<u8> {
        track!(ReadBytesExt::read_u8(self).map_err(Error::from))
    }

    fn read_u16(&mut self) -> Result<u16> {
        track!(ReadBytesExt::read_u16::<LittleEndian>(self).map_err(Error::from))
    }

    fn read_u32(&mut self) -> Result<u32> {
        track!(ReadBytesExt::read_u32::<LittleEndian>(self).map_err(Error::from))
    }

    fn read_u64(&mut self) -> Result<u64> {
        track!(ReadBytesExt::read_u64::<LittleEndian>(self).map_err(Error::from))
    }

    fn read_u128(&mut self) -> Result<u128> {
        track!(ReadBytesExt::read_u128::<LittleEndian>(self).map_err(Error::from))
    }
}
impl<T: Read> ReadExt for T {}
