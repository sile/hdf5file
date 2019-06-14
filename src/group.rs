use crate::level1::{BTreeNode, LocalHeap, SymbolTableEntry};
use crate::Result;
use std::io::Read;

#[derive(Debug)]
pub struct Group {
    b_tree_node: BTreeNode,
    local_heap: LocalHeap,
}
impl Group {
    pub fn new<R: Read>(b_tree_node: BTreeNode, local_heap: LocalHeap) -> Self {
        Self {
            b_tree_node,
            local_heap,
        }
    }

    // pub fn path(&self) -> &Path {
    //     &self.path
    // }
}
