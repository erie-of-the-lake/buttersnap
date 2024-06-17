/*!
 * Integration tests for buttersnap path module.
 */

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

use buttersnap::path::{
    DevPath,
    Mountpoint,
};



use std::path::PathBuf;

#[cfg(test)]
mod devpath_tests {
    use super::*;

    #[test]
    fn new_devpath_is_default_devpath() {
        assert_eq!(DevPath::default(), DevPath::new());
    }

    
    /// Tests different scenarios for [`DevPath::from_path`]
    #[test]
    fn test_devpath_from_path () {

        let dev = PathBuf::from("/dev");
        let dev_null_with_root = PathBuf::from("/dev/null");
        let dev_null_rootless = PathBuf::from("dev/null");

        let home_user_documents = PathBuf::from("/home/user/Documents");

        assert!(
            DevPath::from_path(dev.clone()).is_ok(),
            "`{dev:?}` should be a valid `DevPath`"
        );
        assert!(
            DevPath::from_path(dev_null_with_root.clone()).is_ok(),
            "`{dev_null_with_root:?}` should be a valid `DevPath`"
        );
        assert!(
            DevPath::from_path(dev_null_rootless.clone()).is_err(),
            "`{dev_null_rootless:?}` should error out since it is a relative path"
        );
        assert!(
            DevPath::from_path(home_user_documents.clone()).is_err(),
            "`{home_user_documents:?}` does not even start with `/dev`, and so shouldn't be a `DevPath`"
        );
    }

    #[test]
    fn parent_devpath_follows_symlinks() {
        unimplemented!("Need to create mock filesystem");
    }

    #[test]
    fn parent_devpath_without_symlink_returns_none() {
        unimplemented!("Need to create mock filesystem");
    }

}

#[cfg(test)]
mod mountpoint_tests {

    // Test for [`from_path`](Mountpoint::from_path) function
    // with a nonexistent path
    #[test]
    fn nonexistent_path_leads_to_error_with_check() {
        unimplemented!("Need to create mock filesytem which simulates mount devices");
    }

    #[test]
    fn file_errors_with_check() {
        unimplemented!("Need to create mock filesystem which simulates files");
    }

    // Test for [`from_path_unchecked`](Mountpoint::from_path_unchecked)
    // function with a nonexistent path
    #[test]
    fn nonexistent_path_leads_to_unknown_status_unchecked() {
        unimplemented!("Need to create mock filesystem which simulates mount devices")
    }
}