use crate::io::{ReadExt as _, SeekExt as _};
use crate::{ErrorKind, Result};
use std;
use std::io::{Read, Seek};

const FORMAT_SIGNATURE: [u8; 8] = [137, 72, 68, 70, 13, 10, 26, 10];
const UNDEFINED_ADDRESS: u64 = std::u64::MAX;

#[derive(Debug)]
pub struct Superblock {
    pub group_leaf_node_k: u16,     // TODO: NonZeroU16
    pub group_internal_node_k: u16, // TODO: NonZeroU16
    pub end_of_file_address: u64,
    pub root_group_symbol_table_entry: SymbolTableEntry,
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

// TODO: move level2a
/// https://support.hdfgroup.org/HDF5/doc/H5.format.html#ObjectHeader
#[derive(Debug)]
pub struct ObjectHeader {
    prefix: ObjectHeaderPrefix,
}
impl ObjectHeader {
    pub fn from_reader<R: Read>(mut reader: R) -> Result<Self> {
        let prefix = track!(ObjectHeaderPrefix::from_reader(&mut reader))?;
        Ok(Self { prefix })
    }
}

#[derive(Debug)]
pub struct ObjectHeaderPrefix {
    messages: Vec<HeaderMessage>,
    object_reference_count: u32,
    object_header_size: u32,
}
impl ObjectHeaderPrefix {
    pub fn from_reader<R: Read>(mut reader: R) -> Result<Self> {
        let version = track!(reader.read_u8())?;
        track_assert_eq!(version, 1, ErrorKind::InvalidFile);

        let _reserved = track!(reader.read_u8())?;
        let header_message_count = track!(reader.read_u16())?;
        dbg!(header_message_count);

        let object_reference_count = track!(reader.read_u32())?;
        dbg!(object_reference_count);

        let object_header_size = track!(reader.read_u32())?;
        dbg!(object_header_size);

        let messages = (0..header_message_count)
            .map(|_| track!(HeaderMessage::from_reader(&mut reader)))
            .collect::<Result<_>>()?;

        Ok(Self {
            messages,
            object_reference_count,
            object_header_size,
        })
    }
}

bitflags! {
    struct HeaderMessageFlags: u8 {
        const CONSTANT = 0b0000_0001;
        const SHARED = 0b0000_0010;
        const UNSHARABLE = 0b0000_0100;
        const CANNOT_WRITE_IF_UNKNOWN = 0b0000_1000;
        const SET_5_BIT_IF_UNKNOWN = 0b0001_0000;
        const UNKNOWN_BUT_MODIFIED = 0b0010_0000;
        const SHARABLE = 0b0100_0000;
        const FAIL_IF_UNKNOWN = 0b0100_0000;
    }
}

#[derive(Debug)]
pub struct HeaderMessage {
    kind: u16,
    flags: HeaderMessageFlags,
    data: Vec<u8>,
}
impl HeaderMessage {
    pub fn from_reader<R: Read>(mut reader: R) -> Result<Self> {
        let kind = track!(reader.read_u16())?;
        let data_len = track!(reader.read_u16())?;
        let flags = HeaderMessageFlags::from_bits_truncate(track!(reader.read_u8())?);
        track!(reader.skip(3))?;
        let data = track!(reader.read_vec(data_len as usize))?;
        Ok(Self { kind, flags, data })
    }
}

/// https://support.hdfgroup.org/HDF5/doc/H5.format.html#LocalHeap
#[derive(Debug)]
pub struct LocalHeaps {
    data_segment_size: u64,
    free_list_head_offset: u64,
    data_segment_address: u64,
}
impl LocalHeaps {
    pub fn from_reader<R: Read>(mut reader: R) -> Result<Self> {
        let mut signature = [0; 4];
        track!(reader.read_bytes(&mut signature))?;
        track_assert_eq!(&signature, b"HEAP", ErrorKind::InvalidFile);

        let version = track!(reader.read_u8())?;
        track_assert_eq!(version, 0, ErrorKind::Unsupported);
        track!(reader.skip(3))?;

        let data_segment_size = track!(reader.read_u64())?;
        let free_list_head_offset = track!(reader.read_u64())?;
        let data_segment_address = track!(reader.read_u64())?;
        Ok(Self {
            data_segment_size,
            free_list_head_offset,
            data_segment_address,
        })
    }
}

// TODO: move level1
/// https://support.hdfgroup.org/HDF5/doc/H5.format.html#SymbolTableEntry
#[derive(Debug)]
pub struct SymbolTableEntry {
    link_name_offset: u64,
    object_header_address: u64,
    scratch_pad: ScratchPad,
}
impl SymbolTableEntry {
    pub fn object_header<R: Read + Seek>(&self, mut reader: R) -> Result<ObjectHeader> {
        track!(reader.seek_to(self.object_header_address))?;
        track!(ObjectHeader::from_reader(reader))
    }

    pub fn local_heaps<R: Read + Seek>(&self, mut reader: R) -> Result<LocalHeaps> {
        if let ScratchPad::ObjectHeader {
            name_heap_address, ..
        } = self.scratch_pad
        {
            track!(reader.seek_to(name_heap_address))?;
            track!(LocalHeaps::from_reader(reader))
        } else {
            track_panic!(ErrorKind::Unsupported);
        }
    }

    fn from_reader<R: Read>(mut reader: R) -> Result<Self> {
        let link_name_offset = track!(reader.read_u64())?;
        track_assert_eq!(link_name_offset, 0, ErrorKind::Unsupported);

        let object_header_address = track!(reader.read_u64())?;
        let cache_type = track!(reader.read_u32())?;

        let _reserved = track!(reader.read_u32())?;
        let scratch_pad = track!(ScratchPad::from_reader(cache_type, &mut reader))?;
        Ok(Self {
            link_name_offset,
            object_header_address,
            scratch_pad,
        })
    }
}

#[derive(Debug)]
pub enum ScratchPad {
    None,
    ObjectHeader {
        btree_address: u64,
        name_heap_address: u64,
    },
    SymbolicLink {
        link_value_offset: u32,
    },
}
impl ScratchPad {
    fn from_reader<R: Read>(cache_type: u32, mut reader: R) -> Result<Self> {
        match cache_type {
            0 => {
                let _ = track!(reader.read_u128())?;
                Ok(ScratchPad::None)
            }
            1 => {
                let btree_address = track!(reader.read_u64())?;
                let name_heap_address = track!(reader.read_u64())?;
                Ok(ScratchPad::ObjectHeader {
                    btree_address,
                    name_heap_address,
                })
            }
            2 => {
                let link_value_offset = track!(reader.read_u32())?;
                track!(reader.skip(12))?;
                Ok(ScratchPad::SymbolicLink { link_value_offset })
            }
            _ => track_panic!(ErrorKind::InvalidFile, "Unknown cache type: {}", cache_type),
        }
    }
}
