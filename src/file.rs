use crate::level0::Superblock;
use crate::level1::{BTreeNode, LocalHeap, SymbolTableEntry};
use crate::{ErrorKind, Object, Result};
use std::io::{BufReader, Read, Seek};
use std::path::{Component, Path};

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

    pub fn get_object<P: AsRef<Path>>(&mut self, path: P) -> Result<Option<Object>> {
        let mut node = track!(Node::new(
            BufReader::new(&mut self.io),
            &self.superblock.root_group_symbol_table_entry,
        ))?;

        let mut components = path.as_ref().components();
        track_assert_eq!(
            components.next(),
            Some(Component::RootDir),
            ErrorKind::InvalidInput
        );

        for component in components {
            if let Component::Normal(name) = component {
                let name = track_assert_some!(name.to_str(), ErrorKind::InvalidInput);
                track!(node.get_child(name))?;
            } else {
                track_panic!(ErrorKind::InvalidInput);
            }
        }
        panic!()
    }
}

#[derive(Debug)]
pub struct Node<T> {
    io: T,
    b_tree_node: BTreeNode,
    local_heap: LocalHeap,
}
impl<T> Node<T>
where
    T: Read + Seek,
{
    pub fn new(mut io: T, symbol_table: &SymbolTableEntry) -> Result<Self> {
        let b_tree_node = track!(symbol_table.b_tree_node(&mut io))?;
        let b_tree_node = track_assert_some!(b_tree_node, ErrorKind::InvalidInput);

        let local_heap = track!(symbol_table.local_heaps(&mut io))?;
        let local_heap = track_assert_some!(local_heap, ErrorKind::InvalidInput);
        Ok(Self {
            io,
            b_tree_node,
            local_heap,
        })
    }

    pub fn get_child(&mut self, name: &str) -> Result<Option<()>> {
        panic!()
    }
}
