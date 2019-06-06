use crate::io::ReadExt as _;
use crate::{ErrorKind, Result};
use std;
use std::io::Read;

const FORMAT_SIGNATURE: [u8; 8] = [137, 72, 68, 70, 13, 10, 26, 10];
const UNDEFINED_ADDRESS: u64 = std::u64::MAX;

#[derive(Debug)]
pub struct Superblock {
    group_leaf_node_k: u16,     // TODO: NonZeroU16
    group_internal_node_k: u16, // TODO: NonZeroU16
    end_of_file_address: u64,
    root_group_symbol_table_entry: SymbolTableEntry,
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
        track_assert_eq!(size_of_offsets, 8, ErrorKind::Unsupported);

        let size_of_lengths = track!(reader.read_u8())?;
        track_assert_eq!(size_of_lengths, 8, ErrorKind::Unsupported);

        let _reserved1 = track!(reader.read_u8())?;

        let group_leaf_node_k = track!(reader.read_u16())?;
        let group_internal_node_k = track!(reader.read_u16())?;

        let file_consistency_flags = track!(reader.read_u32())?;
        track_assert_eq!(file_consistency_flags, 0, ErrorKind::Unsupported);

        let base_address = track!(reader.read_u64())?;
        track_assert_eq!(base_address, 0, ErrorKind::Unsupported);

        let address_of_file_free_space_info = track!(reader.read_u64())?;
        track_assert_eq!(
            address_of_file_free_space_info,
            UNDEFINED_ADDRESS,
            ErrorKind::Unsupported
        );

        let end_of_file_address = track!(reader.read_u64())?;

        let driver_information_block_address = track!(reader.read_u64())?;
        track_assert_eq!(
            driver_information_block_address,
            UNDEFINED_ADDRESS,
            ErrorKind::Unsupported
        );

        let root_group_symbol_table_entry = track!(SymbolTableEntry::from_reader(&mut reader))?;
        Ok(Self {
            group_leaf_node_k,
            group_internal_node_k,
            end_of_file_address,
            root_group_symbol_table_entry,
        })
    }
}

// TODO: move level1
/// https://support.hdfgroup.org/HDF5/doc/H5.format.html#SymbolTableEntry
#[derive(Debug)]
pub struct SymbolTableEntry {
    link_name_offset: u64,
    object_header_address: u64,
    cache_type: u32,
    scratch_pad_space: u128,
}
impl SymbolTableEntry {
    fn from_reader<R: Read>(mut reader: R) -> Result<Self> {
        let link_name_offset = track!(reader.read_u64())?;
        let object_header_address = track!(reader.read_u64())?;
        let cache_type = track!(reader.read_u32())?;
        let _reserved = track!(reader.read_u32())?;
        let scratch_pad_space = track!(reader.read_u128())?;
        Ok(Self {
            link_name_offset,
            object_header_address,
            cache_type,
            scratch_pad_space,
        })
    }
}
