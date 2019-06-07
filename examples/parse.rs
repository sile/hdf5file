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

    let h = track!(s.root_group_symbol_table_entry.object_header(&mut file))?;
    println!("Root Object Header: {:?}", h);
    Ok(())
}
