use crate::level0::Superblock;
use crate::level1::{BTreeNode, BTreeNodeChild, LocalHeap, SymbolTableEntry};
use crate::level2::DataObject;
use crate::{Error, ErrorKind, Result};
use std::fs::File;
use std::io::{BufReader, Read, Seek};
use std::path::{Component, Path, PathBuf};

/// HDF5 file.
#[derive(Debug)]
pub struct Hdf5File<T = File> {
    io: T,
    superblock: Superblock,
}
impl Hdf5File<File> {
    /// Makes a new `Hdf5File` instance by opening the specified file.
    pub fn open_file<P: AsRef<Path>>(path: P) -> Result<Self> {
        let file = track!(File::open(path).map_err(Error::from))?;
        track!(Self::open(file))
    }
}
impl<T> Hdf5File<T>
where
    T: Read + Seek,
{
    /// Makes a new `Hdf5File` instance by reading data from the given I/O stream.
    pub fn open(mut io: T) -> Result<Self> {
        let superblock = track!(Superblock::from_reader(&mut io))?;
        Ok(Self { io, superblock })
    }

    /// Returns an iterator that iterates over the paths of all objects stored in the file.
    pub fn object_paths<'a>(&'a mut self) -> Result<impl 'a + Iterator<Item = Result<PathBuf>>> {
        let mut io = BufReader::new(&mut self.io);
        let root = track!(Node::new(
            &mut io,
            &self.superblock.root_group_symbol_table_entry,
        ))?;
        Ok(Objects::new(io, root))
    }

    pub fn get_object<P: AsRef<Path>>(&mut self, path: P) -> Result<Option<DataObject>> {
        let mut io = BufReader::new(&mut self.io);
        let mut node = track!(Node::new(
            &mut io,
            &self.superblock.root_group_symbol_table_entry,
        ))?;

        let mut components = path.as_ref().components().peekable();
        track_assert_eq!(
            components.next(),
            Some(Component::RootDir),
            ErrorKind::InvalidInput
        );

        while let Some(component) = components.next() {
            if let Component::Normal(name) = component {
                let name = track_assert_some!(name.to_str(), ErrorKind::InvalidInput);
                if components.peek().is_some() {
                    if let Some(child) = track!(node.get_dir(&mut io, name))? {
                        node = child;
                    } else {
                        return Ok(None);
                    }
                } else {
                    if let Some(data) = track!(node.get_data(&mut io, name))? {
                        return Ok(Some(data));
                    } else {
                        return Ok(None);
                    }
                }
            } else {
                track_panic!(ErrorKind::InvalidInput);
            }
        }
        track_panic!(ErrorKind::InvalidInput);
    }
}

#[derive(Debug)]
pub struct Node {
    dir: PathBuf,
    b_tree_node: BTreeNode,
    local_heap: LocalHeap,
}
impl Node {
    pub fn new<T>(mut io: T, symbol_table: &SymbolTableEntry) -> Result<Self>
    where
        T: Read + Seek,
    {
        let b_tree_node = track!(symbol_table.b_tree_node(&mut io))?;
        let b_tree_node = track_assert_some!(b_tree_node, ErrorKind::InvalidInput);

        let local_heap = track!(symbol_table.local_heaps(&mut io))?;
        let local_heap = track_assert_some!(local_heap, ErrorKind::InvalidInput);
        Ok(Self {
            dir: PathBuf::from("/"),
            b_tree_node,
            local_heap,
        })
    }

    pub fn try_new<T>(mut io: T, symbol_table: &SymbolTableEntry) -> Result<Option<Self>>
    where
        T: Read + Seek,
    {
        let b_tree_node = track!(symbol_table.b_tree_node(&mut io))?;
        let b_tree_node = if let Some(b_tree_node) = b_tree_node {
            b_tree_node
        } else {
            return Ok(None);
        };

        let local_heap = track!(symbol_table.local_heaps(&mut io))?;
        let local_heap = track_assert_some!(local_heap, ErrorKind::InvalidInput);
        Ok(Some(Self {
            dir: PathBuf::from("/"),
            b_tree_node,
            local_heap,
        }))
    }

    fn get_btree_node_child<T>(&self, mut io: T, name: &str) -> Result<Option<BTreeNodeChild>>
    where
        T: Read + Seek,
    {
        let mut found = false;
        let mut index = 0;
        for key in self
            .b_tree_node
            .keys(self.local_heap.clone(), &mut io)
            .skip(1)
        {
            let key = track!(key)?;

            if name <= key.as_str() {
                found = true;
                break;
            }
            index += 1;
        }
        if !found {
            Ok(None)
        } else {
            let child = track_assert_some!(self.children(&mut io).nth(index), ErrorKind::Other);
            Ok(Some(track!(child)?))
        }
    }

    pub fn get_dir<T>(&self, mut io: T, name: &str) -> Result<Option<Self>>
    where
        T: Read + Seek,
    {
        let child = track!(self.get_btree_node_child(&mut io, name))?;
        match child {
            None => Ok(None),
            Some(BTreeNodeChild::Intermediate(child)) => {
                let child = Self {
                    dir: self.dir.clone(),
                    b_tree_node: child,
                    local_heap: self.local_heap.clone(),
                };
                track!(child.get_dir(io, name))
            }
            Some(BTreeNodeChild::GroupLeaf(child)) => {
                for entry in &child.entries {
                    let child_name = track!(entry.link_name(&mut io, Some(&self.local_heap)))?;
                    let child_name = track_assert_some!(child_name, ErrorKind::InvalidFile);
                    if child_name == name {
                        let mut child = track!(Node::new(&mut io, &entry))?;
                        child.dir = self.dir.clone();
                        child.dir.push(name);
                        return Ok(Some(child));
                    }
                }
                Ok(None)
            }
        }
    }

    pub fn get_data<T>(&self, mut io: T, name: &str) -> Result<Option<DataObject>>
    where
        T: Read + Seek,
    {
        let child = track!(self.get_btree_node_child(&mut io, name))?;
        match child {
            None => Ok(None),
            Some(BTreeNodeChild::Intermediate(child)) => {
                let child = Self {
                    dir: self.dir.clone(),
                    b_tree_node: child,
                    local_heap: self.local_heap.clone(),
                };
                track!(child.get_data(io, name))
            }
            Some(BTreeNodeChild::GroupLeaf(child)) => {
                for entry in &child.entries {
                    let child_name = track!(entry.link_name(&mut io, Some(&self.local_heap)))?;
                    let child_name = track_assert_some!(child_name, ErrorKind::InvalidFile);
                    if child_name == name {
                        let data = track!(entry.get_data_object(&mut io))?;
                        return Ok(Some(data));
                    }
                }
                Ok(None)
            }
        }
    }

    pub fn children<'a, T>(&'a self, io: T) -> impl 'a + Iterator<Item = Result<BTreeNodeChild>>
    where
        T: 'a + Read + Seek,
    {
        self.b_tree_node.children(io)
    }
}

#[derive(Debug)]
struct Objects<T> {
    io: T,
    nodes: Vec<Node>,
    paths: Vec<PathBuf>,
}
impl<T> Objects<T>
where
    T: Read + Seek,
{
    fn new(io: T, root: Node) -> Self {
        Self {
            io,
            nodes: vec![root],
            paths: Vec::new(),
        }
    }

    fn next_object_path(&mut self) -> Result<Option<PathBuf>> {
        if let Some(path) = self.paths.pop() {
            return Ok(Some(path));
        }

        while let Some(node) = self.nodes.pop() {
            for child in node.children(&mut self.io).collect::<Vec<_>>() {
                let child = track!(child)?;
                match child {
                    BTreeNodeChild::Intermediate(child) => {
                        let child = Node {
                            dir: node.dir.clone(),
                            b_tree_node: child,
                            local_heap: node.local_heap.clone(),
                        };
                        self.nodes.push(child);
                    }
                    BTreeNodeChild::GroupLeaf(child) => {
                        for entry in &child.entries {
                            let name =
                                track!(entry.link_name(&mut self.io, Some(&node.local_heap)))?;
                            let name = track_assert_some!(name, ErrorKind::InvalidFile);

                            let mut path = node.dir.clone();
                            path.push(name);
                            self.paths.push(path.clone());

                            if let Some(mut grand_child) =
                                track!(Node::try_new(&mut self.io, &entry))?
                            {
                                grand_child.dir = path;
                                self.nodes.push(grand_child);
                            }
                        }
                    }
                }
            }
            if !self.paths.is_empty() {
                break;
            }
        }

        Ok(self.paths.pop())
    }
}
impl<T> Iterator for Objects<T>
where
    T: Read + Seek,
{
    type Item = Result<PathBuf>;

    fn next(&mut self) -> Option<Self::Item> {
        track!(self.next_object_path()).transpose()
    }
}
