use crate::io::ReadExt as _;
use crate::{ErrorKind, Result};
use std::io::Read;

const FORMAT_SIGNATURE: [u8; 8] = [137, 72, 68, 70, 13, 10, 26, 10];

#[derive(Debug)]
pub struct Superblock {
    size_of_offsets: u8,
    size_of_lengths: u8,
    group_leaf_node_k: u16,
    group_internal_node_k: u16,
}
impl Superblock {
    pub fn from_reader<R: Read>(mut reader: R) -> Result<Self> {
        let mut signature = [0; 8];
        track!(reader.read_bytes(&mut signature))?;
        track_assert_eq!(signature, FORMAT_SIGNATURE, ErrorKind::InvalidFile);

        let superblock_version = track!(reader.read_u8())?;
        track_assert_eq!(superblock_version, 0, ErrorKind::Unsupported);

        let free_space_storage_version = track!(reader.read_u8())?;
        track_assert_eq!(free_space_storage_version, 0, ErrorKind::Unsupported);

        let root_group_symbol_table_entry_version = track!(reader.read_u8())?;
        track_assert_eq!(
            root_group_symbol_table_entry_version,
            0,
            ErrorKind::Unsupported
        );
        let _reserved0 = track!(reader.read_u8())?;

        let shared_header_message_format_version = track!(reader.read_u8())?;
        track_assert_eq!(
            shared_header_message_format_version,
            0,
            ErrorKind::Unsupported
        );

        let size_of_offsets = track!(reader.read_u8())?;
        let size_of_lengths = track!(reader.read_u8())?;
        let _reserved1 = track!(reader.read_u8())?;

        let group_leaf_node_k = track!(reader.read_u16())?;
        let group_internal_node_k = track!(reader.read_u16())?;

        Ok(Self {
            size_of_offsets,
            size_of_lengths,
            group_leaf_node_k,
            group_internal_node_k,
        })
    }
}
