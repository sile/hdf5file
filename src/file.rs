use crate::level0::Superblock;
use crate::level1::{BTreeNode, BTreeNodeChild, LocalHeap, SymbolTableEntry};
use crate::{ErrorKind, Object, Result};
use std::io::{BufReader, Read, Seek};
use std::path::{Component, Path, PathBuf};

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
        let mut io = BufReader::new(&mut self.io);
        let mut node = track!(Node::new(
            &mut io,
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
                loop {
                    if let Some((do_break, child)) = track!(node.get_child(&mut io, name))? {
                        node = child;
                        if do_break {
                            break;
                        }
                    } else {
                        return Ok(None);
                    }
                }
            } else {
                track_panic!(ErrorKind::InvalidInput);
            }
        }
        panic!()
    }

    pub fn objects<'a>(&'a mut self) -> Result<impl 'a + Iterator<Item = Result<PathBuf>>> {
        let mut io = BufReader::new(&mut self.io);
        let root = track!(Node::new(
            &mut io,
            &self.superblock.root_group_symbol_table_entry,
        ))?;
        Ok(Objects::new(io, root))
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

    pub fn get_child<T>(&mut self, mut io: T, name: &str) -> Result<Option<(bool, Self)>>
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
            return Ok(None);
        }

        let child = track_assert_some!(self.children(&mut io).nth(index), ErrorKind::Other);
        match track!(child)? {
            BTreeNodeChild::Intermediate(child) => {
                let child = Self {
                    dir: self.dir.clone(),
                    b_tree_node: child,
                    local_heap: self.local_heap.clone(),
                };
                Ok(Some((false, child)))
            }
            BTreeNodeChild::GroupLeaf(child) => {
                // let mut child = track!(Node::new(&mut io, &child))?;
                // child.dir = self.dir.clone();
                // child.dir.push(name);
                // Ok(Some((true, child)))
                unimplemented!("{:?}", child);
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
pub struct Objects<T> {
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
