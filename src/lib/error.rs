
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
    clippy::print_stderr,
    clippy::print_stdout,
    clippy::string_to_string,
    clippy::undocumented_unsafe_blocks,
    clippy::unneeded_field_pattern,
)]

// external imports
use thiserror::Error;

// std imports
use std::path::PathBuf;

/// Generic result type where `ButterResult<T> = Result<T, ButterError>`
/// for any generic type `T`.
pub type ButterResult<T> = Result<T, ButterError>;

/// Generic [`Error`] type for crate. 
/// 
/// **NOTE:** This type should be listed as `#[non_exhaustive]` until a stable release is used.
#[non_exhaustive]
#[derive(Debug, Error)]
pub enum ButterError {

    // ----- External Errors ----- //

    /// Errors from the [`libbtrfsutil`] crate.
    #[error(transparent)]
    BtrfsError(libbtrfsutil::Error),

    /// Errors from the [`block_utils`] crate.
    #[error(transparent)]
    BlockUtilsError(block_utils::BlockUtilsError),

    /// Errors from the [`uuid`] crate.
    #[error(transparent)]
    UuidParseError(uuid::Error),

    
    // ----- Path-Related Errors ----- //

    /// Describes general and misc. errors related to the Linux system path.
    #[error("Invalid path of `{}` : {}", 
            path.to_string_lossy(), 
            reason)]
    InvalidPath {
        path: PathBuf,
        reason: String,
    },

    // ----- Devpath-Related Errors ----- //

    /// Describes errors which arise from an invalid Linux path tarting at `/dev`
    #[error("Invalid path at `/dev` : `{}` does not exist", 
            .0.display() )]
    InvalidDevpath(PathBuf),
    
    /// Describes errors where a path at `/dev` does not have a parent.
    /// (i.e. it is not a symlink to some other [`Path`]) 
    #[error("Invalid path at `/dev` : `{}` does not have a parent path", 
            .0.display() )]
    InvalidParentDevpath(PathBuf),

    // ----- Mountpoint-Related Errors ----- //
    
    /// Describes situations where a [`Mountpoint`] for a block device or BTRFS subvolume
    /// does not exist, is not an actual mountpoint (e.g. is not a directory), etc.
    #[error("Invalid mountpoint : '{}' is not recognized", 
            .0.display() )]
    InvalidMountpoint(PathBuf),

    // ----- Device-Related & UUID-Related Errors ----- //

    /// Describes an invalid [UUID](uuid::Uuid) which does not exist,
    /// was input improperly, etc.
    #[error("Invalid UUID : '{}' does not exist", 
            .0.hyphenated().to_string() )]
    InvalidUuid(uuid::Uuid), 

    /// Describes a situation where a block device does not have a [UUID](uuid::Uuid).
    #[error("Device `{}` does not have a UUID",
            .0.to_string_lossy() )]
    DeviceMissingUuid(PathBuf),

    // ----- Misc. Errors ----- //

    /// Miscellaneous error type. This usually describes an error related to parsing.
    #[error("{0}")]
    Other(String),


}

/// Use `impl_from_error_for_butter_error` to minimize boilerplate.
///
/// Converts `From<Error>` to `ButterError` such that `?` operator
/// can be used for error propagation
macro_rules! impl_from_error_for_butter_error {
    ( $( $ExternalCrateError:ty => $ButterErrorPlusVariant:expr ;)* ) => {$(

        impl From<$ExternalCrateError> for ButterError {
            fn from(error: $ExternalCrateError) -> Self {
                $ButterErrorPlusVariant(error)
            }
        }
        
    )*}
}

// now add `From<Error>` impls for all variants in `ButterError`
impl_from_error_for_butter_error!(
    block_utils::BlockUtilsError => ButterError::BlockUtilsError;
    libbtrfsutil::Error          => ButterError::BtrfsError;
    uuid::Error                  => ButterError::UuidParseError;
);




