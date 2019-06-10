#[macro_use]
extern crate trackable;

use hdf5file;
use std::fs::File;
use std::path::PathBuf;
use structopt::StructOpt;

#[derive(Debug, StructOpt)]
struct Opt {
    path: PathBuf,
}

fn main() -> trackable::result::TopLevelResult {
    let opt = Opt::from_args();
    let mut file = track_any_err!(File::open(&opt.path); opt.path)?;

    let s = track!(hdf5file::level0::Superblock::from_reader(&mut file))?;
    println!("Superblock: {:?}", s);
    println!(
        "Root Link Name: {:?}",
        s.root_group_symbol_table_entry.link_name(&mut file, None)?
    );

    let h = track!(s.root_group_symbol_table_entry.object_header(&mut file))?;
    println!("Root Object Header: {:?}", h);

    let h = track!(s.root_group_symbol_table_entry.local_heaps(&mut file))?;
    let h = track_assert_some!(h, trackable::error::Failed);
    println!("Local Heaps: {:?}", h);

    let b = track!(s.root_group_symbol_table_entry.b_tree_node(&mut file))?;
    let b = track_assert_some!(b, trackable::error::Failed);
    println!("B-Tree Node: {:?}", b);

    for k in b.keys(h.clone(), &mut file) {
        println!("  - Key: {:?}", track!(k)?);
    }

    let mut stack = vec![b];
    while let Some(node) = stack.pop() {
        for c in node.children(&mut file).collect::<Vec<_>>().into_iter() {
            match track!(c)? {
                hdf5file::level0::BTreeNodeChild::Intermediate(c) => {
                    stack.push(c);
                }
                hdf5file::level0::BTreeNodeChild::GroupLeaf(c) => {
                    for entry in &c.entries {
                        println!("# {:?}", entry);
                        println!("# {:?}", entry.object_header(&mut file)?);
                        println!(
                            "# LINK_NAME: {:?}",
                            track!(entry.link_name(&mut file, Some(&h))).ok()
                        );

                        let node = entry.b_tree_node(&mut file)?;
                        let heap = entry.local_heaps(&mut file)?;
                        println!("# {:?}", node);
                        let (node, heap) = if let (Some(n), Some(h)) = (node, heap) {
                            (n, h)
                        } else {
                            continue;
                        };
                        for k in node.keys(heap.clone(), &mut file) {
                            println!("  - Key: {:?}", track!(k)?);
                        }
                        for c in node.children(&mut file).collect::<Vec<_>>().into_iter() {
                            let c = c?;
                            println!("  # {:?}", c);
                            if let hdf5file::level0::BTreeNodeChild::GroupLeaf(c) = c {
                                for entry in &c.entries {
                                    println!("  # {:?}", entry.object_header(&mut file)?);
                                    println!(
                                        "  # {:?}: Name: {:?}",
                                        entry,
                                        entry.link_name(&mut file, Some(&heap))?
                                    );
                                }
                            }
                        }
                    }
                    // panic!();
                }
            }
        }
        println!("STACK: {}", stack.len());
    }
    Ok(())
}
