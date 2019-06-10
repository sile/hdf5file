use crate::{Error, ErrorKind, Result};
use byteorder::{LittleEndian, ReadBytesExt};
use std::io::{Read, Seek, SeekFrom};

pub trait SeekExt: Seek {
    fn seek_to(&mut self, offset: u64) -> Result<()> {
        track!(self.seek(SeekFrom::Start(offset)).map_err(Error::from))?;
        Ok(())
    }
}
impl<T: Seek> SeekExt for T {}

pub trait ReadExt: Read {
    fn assert_signature(&mut self, expected: &[u8]) -> Result<()> {
        let mut signature = [0; 4];
        track!(self.read_bytes(&mut signature))?;
        track_assert_eq!(&signature, expected, ErrorKind::InvalidFile);
        Ok(())
    }

    fn read_all(&mut self) -> Result<Vec<u8>> {
        let mut buf = Vec::new();
        track!(self.read_to_end(&mut buf).map_err(Error::from))?;
        Ok(buf)
    }

    fn skip(&mut self, n: usize) -> Result<()> {
        for _ in 0..n {
            track!(self.read_u8())?;
        }
        Ok(())
    }

    fn read_null_terminated_string(&mut self) -> Result<String> {
        let mut buf = Vec::new();
        loop {
            let b = track!(self.read_u8())?;
            if b == 0 {
                break;
            } else {
                buf.push(b);
            }
        }
        track!(String::from_utf8(buf).map_err(Error::from))
    }

    fn read_bytes(&mut self, buf: &mut [u8]) -> Result<()> {
        track!(self.read_exact(buf).map_err(Error::from))
    }

    fn read_vec(&mut self, n: usize) -> Result<Vec<u8>> {
        let mut bytes = vec![0; n];
        track!(self.read_bytes(&mut bytes))?;
        Ok(bytes)
    }

    fn read_u8(&mut self) -> Result<u8> {
        track!(ReadBytesExt::read_u8(self).map_err(Error::from))
    }

    fn read_u16(&mut self) -> Result<u16> {
        track!(ReadBytesExt::read_u16::<LittleEndian>(self).map_err(Error::from))
    }

    fn read_u24(&mut self) -> Result<u32> {
        track!(ReadBytesExt::read_u24::<LittleEndian>(self).map_err(Error::from))
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
