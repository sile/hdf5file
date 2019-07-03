use crate::io::{ReadExt as _, SeekExt as _};
use crate::lowlevel::level2::{DataObject, ObjectHeader};
use crate::{Error, ErrorKind, Result};
use itertools::Either;
use std;
use std::convert::TryFrom;
use std::io::{Read, Seek};

/// https://support.hdfgroup.org/HDF5/doc/H5.format.html#LocalHeap
#[derive(Debug, Clone)]
pub struct LocalHeap {
    data_segment_size: u64,
    free_list_head_offset: u64,
    data_segment_address: u64,
}
impl LocalHeap {
    pub fn read_string<R: Read + Seek>(&self, offset: u64, mut reader: R) -> Result<String> {
        track!(reader.seek_to(self.data_segment_address + offset))?;
        track!(reader.read_null_terminated_string())
    }

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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum NodeType {
    Group = 0,
    RawDataChunk = 1,
}
impl TryFrom<u8> for NodeType {
    type Error = Error;

    fn try_from(f: u8) -> Result<Self> {
        match f {
            0 => Ok(NodeType::Group),
            1 => Ok(NodeType::RawDataChunk),
            _ => track_panic!(ErrorKind::InvalidFile, "Unknown node type: {}", f),
        }
    }
}

/// https://support.hdfgroup.org/HDF5/doc/H5.format.html#Btrees
#[derive(Debug, Clone)]
pub enum BTreeNode {
    Group {
        node_level: u8,
        keys: Vec<u64>,
        left_sibling_address: u64,
        right_sibling_address: u64,
        children: Vec<u64>,
    },
}
impl BTreeNode {
    pub fn from_reader<R: Read>(mut reader: R) -> Result<Self> {
        let mut signature = [0; 4];
        track!(reader.read_bytes(&mut signature))?;
        track_assert_eq!(&signature, b"TREE", ErrorKind::InvalidFile);

        let node_type = track!(reader.read_u8().and_then(NodeType::try_from))?;
        track_assert_eq!(node_type, NodeType::Group, ErrorKind::Unsupported);

        let node_level = track!(reader.read_u8())?;
        let entries_used = track!(reader.read_u16())?;

        let left_sibling_address = track!(reader.read_u64())?;
        let right_sibling_address = track!(reader.read_u64())?;

        let mut keys = Vec::with_capacity(entries_used as usize + 1);
        let mut children = Vec::with_capacity(entries_used as usize);
        for _ in 0..entries_used {
            keys.push(track!(reader.read_u64())?);
            children.push(track!(reader.read_u64())?);
        }
        keys.push(track!(reader.read_u64())?);

        Ok(BTreeNode::Group {
            node_level,
            keys,
            children,
            left_sibling_address,
            right_sibling_address,
        })
    }

    pub fn children<'a, R: 'a + Read + Seek>(
        &'a self,
        mut reader: R,
    ) -> impl 'a + Iterator<Item = Result<BTreeNodeChild>> {
        let BTreeNode::Group {
            node_level,
            children,
            ..
        } = self;
        if *node_level == 0 {
            Either::Left(children.iter().map(move |&addr| {
                track!(reader.seek_to(addr))?;
                track!(SymbolTableNode::from_reader(&mut reader)).map(BTreeNodeChild::GroupLeaf)
            }))
        } else {
            Either::Right(children.iter().map(move |&addr| {
                track!(reader.seek_to(addr))?;
                track!(Self::from_reader(&mut reader)).map(BTreeNodeChild::Intermediate)
            }))
        }
    }

    pub fn keys<'a, R: 'a + Read + Seek>(
        &'a self,
        heap: LocalHeap,
        mut reader: R,
    ) -> impl 'a + Iterator<Item = Result<String>> {
        let BTreeNode::Group { keys, .. } = self;
        keys.iter()
            .map(move |&addr| track!(heap.read_string(addr, &mut reader)))
    }
}

/// https://support.hdfgroup.org/HDF5/doc/H5.format.html#SymbolTable
#[derive(Debug, Clone)]
pub struct SymbolTableNode {
    pub entries: Vec<SymbolTableEntry>,
}
impl SymbolTableNode {
    pub fn from_reader<R: Read>(mut reader: R) -> Result<Self> {
        track!(reader.assert_signature(b"SNOD"))?;
        let version = track!(reader.read_u8())?;
        track_assert_eq!(version, 1, ErrorKind::Unsupported);
        track!(reader.skip(1))?;
        let symbol_count = track!(reader.read_u16())?;
        let entries = (0..symbol_count)
            .map(|_| track!(SymbolTableEntry::from_reader(&mut reader)))
            .collect::<Result<_>>()?;
        Ok(Self { entries })
    }
}

#[derive(Debug, Clone)]
pub enum BTreeNodeChild {
    Intermediate(BTreeNode),
    GroupLeaf(SymbolTableNode),
}

// TODO: move level1
/// https://support.hdfgroup.org/HDF5/doc/H5.format.html#SymbolTableEntry
#[derive(Debug, Clone)]
pub struct SymbolTableEntry {
    link_name_offset: u64,
    object_header_address: u64,
    scratch_pad: ScratchPad,
}
impl SymbolTableEntry {
    pub fn get_data_object<R: Read + Seek>(&self, mut reader: R) -> Result<DataObject> {
        let header = track!(self.object_header(&mut reader))?;
        track!(header.get_data_object(&mut reader))
    }

    pub fn link_name<R: Read + Seek>(
        &self,
        mut reader: R,
        heap: Option<&LocalHeap>,
    ) -> Result<Option<String>> {
        let mut addr = if let Some(heap) = heap {
            heap.data_segment_address
        } else if let ScratchPad::ObjectHeader {
            name_heap_address, ..
        } = self.scratch_pad
        {
            name_heap_address
        } else {
            return Ok(None);
        };

        addr += self.link_name_offset;
        track!(reader.seek_to(addr))?;

        track!(reader.read_null_terminated_string()).map(Some)
    }

    pub fn object_header<R: Read + Seek>(&self, mut reader: R) -> Result<ObjectHeader> {
        track!(reader.seek_to(self.object_header_address))?;
        track!(ObjectHeader::from_reader(reader))
    }

    pub fn b_tree_node<R: Read + Seek>(&self, mut reader: R) -> Result<Option<BTreeNode>> {
        if let ScratchPad::ObjectHeader { btree_address, .. } = self.scratch_pad {
            track!(reader.seek_to(btree_address))?;
            track!(BTreeNode::from_reader(reader)).map(Some)
        } else {
            // TODO: find header messages
            Ok(None)
        }
    }

    pub fn local_heap<R: Read + Seek>(&self, mut reader: R) -> Result<Option<LocalHeap>> {
        if let ScratchPad::ObjectHeader {
            name_heap_address, ..
        } = self.scratch_pad
        {
            track!(reader.seek_to(name_heap_address))?;
            track!(LocalHeap::from_reader(reader)).map(Some)
        } else {
            // TODO: find header messages
            Ok(None)
        }
    }

    pub fn from_reader<R: Read>(mut reader: R) -> Result<Self> {
        let link_name_offset = track!(reader.read_u64())?;
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

#[derive(Debug, Clone)]
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
