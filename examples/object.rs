#[macro_use]
extern crate trackable;

use hdf5file;
use std::path::PathBuf;
use structopt::StructOpt;

#[derive(Debug, StructOpt)]
struct Opt {
    hdf5_file: PathBuf,

    #[structopt(subcommand)]
    op: Op,
}

#[derive(Debug, StructOpt)]
#[structopt(rename_all = "kebab-case")]
enum Op {
    Get { object_path: PathBuf },
    Ls,
}

fn main() -> trackable::result::TopLevelResult {
    let opt = Opt::from_args();
    let mut file = track!(hdf5file::Hdf5File::open_file(&opt.hdf5_file))?;
    match opt.op {
        Op::Get { object_path } => {
            let object = track!(file.get_object(object_path))?;
            println!("{:?}", object);
        }
        Op::Ls => {
            for object_path in track!(file.object_paths())? {
                println!(
                    "{}",
                    track_assert_some!(track!(object_path)?.to_str(), trackable::error::Failed)
                );
            }
        }
    }
    Ok(())
}
