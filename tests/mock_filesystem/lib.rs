
// super pedantic clippy linter
#![warn(
    clippy::all,
    clippy::complexity,
    clippy::correctness,
    clippy::pedantic,
    clippy::perf,
    clippy::suspicious,
    // misc. clippy
    clippy::nursery,
    clippy::cargo,
)]

#![deny(clippy::correctness)]
#![allow(clippy::module_name_repetitions)]

// clippy restrictions
#![warn(
    clippy::allow_attributes_without_reason,
    clippy::as_underscore,
    clippy::create_dir,
    clippy::map_err_ignore,
    clippy::missing_docs_in_private_items,
    clippy::print_stderr,
    clippy::print_stdout,
    clippy::string_to_string,
    clippy::undocumented_unsafe_blocks,
    clippy::unneeded_field_pattern,
)]


// IMPORTS 
use filesystem::{
    DirEntry,
    FileSystem,
    FakeFileSystem,
    ReadDir
};

// std imports
use std::path::{Path, PathBuf};

pub trait FileOperationChaining: FileSystem {

    /// Creates a directory and returns [`FileSystem`] object.
    /// 
    /// # Panics
    /// Panics when a directory fails to be created.
    fn new_directory(&mut self, path: impl AsRef<Path>) -> &Self {
        self.create_dir(path).unwrap();

        self
    }

    /// Changes current directory and returns [`FileSystem`] object.
    /// 
    /// # Panics
    /// Panics when a current directory cannot be set.
    fn change_directory(&mut self, path: impl AsRef<Path>) -> &Self {
        self.set_current_dir(path).unwrap();

        self
    }

    /// Creates a directory and returns [`FileSystem`] whose current directory is `path`.
    fn into_new_directory(&mut self, path: impl AsRef<Path>) -> &Self {
        self.new_directory(path)
            .change_directory(path)
    }


    /// Writes `buf` (or file's contents) at `path` and reads the file's contents.
    /// 
    /// # Panics
    /// - A file or directory already exists at `path`.
    /// - The parent directory of `path` does not exist.
    /// - Current user has insufficient permissions.
    fn create_and_read_file<P, B>(&mut self, path: P, buf: B) -> Vec<u8>
    where
        P: AsRef<Path>,
        B: AsRef<[u8]>
    {
        self.create_file(path, buf).unwrap();
        
        self.read_file(path).unwrap()
    }

    /// Writes `buf` (or file's contents) to a new or existing file at `buf`
    /// and then reads said contents.
    /// 
    /// # Panics
    /// - The parent directory of `path` does not exist.
    /// - Current user has insufficient permissions.
    fn write_and_read_file<P, B>(&mut self, path: P, buf: B) -> Vec<u8>
    where
        P: AsRef<Path>,
        B: AsRef<[u8]>
    {
        self.write_file(path, buf).unwrap();
        
        self.read_file(path).unwrap()
    }

    /// Writes `buf` (or file's contents) to a new or existing file at `buf`. 
    /// This action overwrites any existing contents that already exist.
    /// Finally, the file's contents are read.
    /// 
    /// # Panics
    /// - The node at `file` (e.g. `example.txt` at `/etc/example.txt`) is a directory.
    /// - The `file` in question does not exist.
    /// - Current user has insufficient permissions.
    fn overwrite_and_read_file<P, B>(&mut self, path: P, buf: B) -> Vec<u8>
    where
        P: AsRef<Path>,
        B: AsRef<[u8]>
    {
        self.overwrite_file(path, buf).unwrap();

        self.read_file(path).unwrap()
    }
}

impl FileOperationChaining for FakeFileSystem {}

// create basic linux filesystem
fn mock_filesystem_setup() -> FakeFileSystem {

    // create root dirs
    let mut btrfs_filesystem = FakeFileSystem::new()
        .into_new_directory("/")
        .new_directory("/root")
        .new_directory("/boot")
        .new_directory("/home")
        .new_directory("/mnt" )
        .new_directory("/proc")
        .new_directory("/sys" )
        .new_directory("/bin" )
        .new_directory("/sbin")
        .new_directory("/lib" )
        .into_new_directory("/usr")
            .new_directory("bin")
            .new_directory("include")
            .new_directory("lib")
            .new_directory("sbin");

    btrfs_filesystem.change_directory("/var")
        .new_directory("cache")
        .new_directory("log")
        .new_directory("spool")
        .new_directory("tmp");

    btrfs_filesystem.change_directory("/home")
        .into_new_directory("user")
            .new_directory("Documents")
            .new_directory("Downloads")
            .new_directory("Music")
            .new_directory("Pictures")
    
    

}
