/*!
 * TODO: make docstring for module
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

// internal imports
use crate::error::*;

// external imports
use block_utils as block;
use type_rules::{Rule, Validator};
use uuid::Uuid;

// std imports
use std::{
    borrow::Cow,
    cmp::Ordering,
    ffi::{OsStr, OsString},
    path::{Path, PathBuf, Component, Components}, str::FromStr,
};

// ====================================================================================
// -------------------------------------- TESTS ---------------------------------------
// ====================================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // -----=[ DEVPATH TESTS ]=----- //
    /*
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
    */
    #[test]
    fn test_devpath_partial_ord() {

        let dev = DevPath::from_str(DEV)
            .expect("Invalid devpath of {DEV}");
        let dev_disk_by_label = DevPath::from_str(DEV_DISK_BY_LABEL)
            .expect("Invalid devpath of {DEV_DISK_BY_LABEL}");
        let dev_null = DevPath::from_str("/dev/null")
            .expect("Invalid devpath of {dev_null}");

        let disk_foobar = DEV_DISK_BY_LABEL.to_owned() + "/foobar";
        let disk_foobar = DevPath::from_str(disk_foobar.as_str())
            .expect("Invalid devpath of {disk_foobar}");

        assert!(dev < dev_disk_by_label);
        assert!(disk_foobar > dev_disk_by_label);
        assert!(disk_foobar == disk_foobar);
        assert!(dev_disk_by_label < dev_null);
    }



    // -----=[ MOUNTPOINT TESTS ]=----- //


}

// ====================================================================================
// ------------------------------------- CONSTANTS ------------------------------------
// ====================================================================================

/// `/`
pub const OS_SEPARATOR: &str = "/";
/// `/` Linux [path](Path)
pub const ROOT: &str = OS_SEPARATOR;

/// `/dev` Linux [path](Path)
pub const DEV: &str = "/dev";
/// Directory containing a list of block devices by [UUID](Uuid).
const DEV_DISK_BY_UUID: &str = "/dev/disk/by-uuid";
/// Directory containing a list of block devices which have a name/label.
const DEV_DISK_BY_LABEL: &str = "/dev/disk/by-label";

// ====================================================================================
// -------------------------------------- DEVPATH -------------------------------------
// ====================================================================================

/// Rule to make sure that only paths with a certain ancestor,
/// e.g. `/dev/` are valid in structs which implement this trait.
#[derive(Debug)]
struct HasAncestor(&'static str);
    
impl<P> Rule<P> for HasAncestor
where
    P: AsRef<Path>,
{
    fn check(&self, value: &P) -> Result<(), String> {
        let ancestor = PathBuf::from(self.0);

        let value: &Path = value.as_ref();
        let value: PathBuf = value.into();

        // takes advantage of partial ordering
        if ancestor > value {
            return Err(format!(
                "{value:?} does not have an ancestor in {ancestor:?}"
            ));
        }
        Ok(())
    }
}

/// A Unix-like path starting with `/dev/`. This is a thin wrapper around
/// [`PathBuf`].
#[derive(Debug, Clone, Validator)]
pub struct DevPath(#[rule(HasAncestor(DEV))] PathBuf);

impl DevPath {

    /// Creates new default [`DevPath`] instance, equivalent to `/dev`.
    #[must_use]
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }

    /// Returns a [`DevPath`] instance from a [`Path`] (or something which implements
    /// [`AsRef<Path>`]).
    /// 
    /// # Errors
    /// The function will return an error if the [`Path`] does not start with `/dev`
    /// or is not an absolute path.
    pub fn from_path(path: impl AsRef<Path>) -> ButterResult<Self> {
        let path: PathBuf = path.as_ref().to_path_buf();
        let devpath: Self = Self(path);

        match devpath.check_validity() {
            Ok(()) => Ok(devpath),
            Err(_string) => Err(ButterError::InvalidPath {
                path: devpath.0,
                reason: "path does not constitute a valid path starting at `/dev`"
                            .to_string(),
            }),
        }
    }

    /// Returns a [`DevPath`] from a [`UUID`](Uuid). Note that this function does not
    /// verify whether the [`DevPath`] actually exists.
    /// 
    /// # Example
    /// ```rust
    /// # use uuid::uuid;
    /// # use std::path::PathBuf;
    /// # use buttersnap::path::DevPath;
    /// // example UUID
    /// let uuid = uuid!("67e55044-10b1-426f-9247-bb680e5fe0c8");
    /// let uuid_devpath = DevPath::from_uuid(uuid);
    /// 
    /// assert_eq!(
    ///     Some(uuid_devpath), 
    ///     DevPath::from_path(PathBuf::from(
    ///         "/dev/disk/by-uuid/67e55044-10b1-426f-9247-bb680e5fe0c8"
    ///     )).ok()
    /// );
    /// ```
    #[must_use]
    pub fn from_uuid(uuid: Uuid) -> Self {
        let uuid_string: String = uuid  // Uuid
            .hyphenated()  // -> Hyphenated
            .to_string();  // -> String
        let uuid_str: &str = uuid_string.as_str();

        Self(PathBuf::from(
            [DEV_DISK_BY_UUID, uuid_str].join(OS_SEPARATOR),
        ))
    }


    /// Finds the greatest ancestor [`DevPath`] instance for a given [`DevPath`]
    /// 
    /// # Example
    /// Suppose a partition named `boot` is located at parition 2 for `/dev/sda`. Then,
    /// ```no_run
    /// # fn main() -> buttersnap::error::ButterResult<()> {
    /// # use buttersnap::path::DevPath;
    /// # use std::ffi::OsString;
    /// let boot_partition = DevPath::from_path(OsString::from(
    ///     "/dev/disk/by-label/boot"
    /// ))?;
    /// let sda_partition_2 = DevPath::from_path(OsString::from(
    ///     "/dev/sda2"
    /// ))?;
    /// assert_eq!(Some(sda_partition_2), DevPath::parent_devpath(&boot_partition));
    /// # Ok(())
    /// # }
    /// ```
    #[must_use]
    pub fn parent_devpath(&self) -> Option<Self> {
        let mut current_devpath = self.clone();

        // we use `current_devpath.0` since current_devpath does not have access
        // to this function
        while current_devpath.0.is_symlink() {
            let symlink: PathBuf = current_devpath.0.read_link().ok()?;

            current_devpath = match Self::from_path(symlink) {
                Ok(devpath) => devpath,
                Err(_) => break,
            }
        }

        Some(current_devpath)
    }

    /// Returns reference to [`Path`]
    #[must_use]
    #[inline]
    pub fn as_path(&self) -> &Path {
        self.0.as_ref()
    }

    /// Returns reference to [`PathBuf`]
    #[must_use]
    #[inline]
    pub const fn as_path_buf(&self) -> &PathBuf {
        &(self.0)
    }

    /// Returns owned [`PathBuf`]
    #[must_use]
    #[inline]
    pub fn to_path_buf(&self) -> PathBuf {
        self.0.clone()
    }


}

impl Default for DevPath {
    /// Returns equivalent to `/dev` for Path
    #[inline]
    fn default() -> Self {
        Self( PathBuf::from(DEV) )
    }
}
        
/// Implements [`AsRef<P>`] for any type `P` which implements [`AsRef<Path>`]
///
/// **NOTE**: [`AsRef<P>`] is a bound introduced on [`PathBuf`] so that
///  `path.as_ref(): &PathBuf -> &P`
impl<P> AsRef<P> for DevPath
where
    P: AsRef<Path>,
    PathBuf: AsRef<P>,
{
    fn as_ref(&self) -> &P {
        let path: &PathBuf = &self.0;
        path.as_ref()
    }
}

/// Macro to implement [`TryFrom`] for multiple types. This exists to stay DRY.
macro_rules! impl_try_from_for_devpath {
    ( $( $Ty:ty ;)+ ) => {$(

        impl TryFrom<$Ty> for DevPath {
            type Error = ButterError;

            #[doc = concat!("Converts from [`", stringify!($Ty), "`] to [`DevPath`]")]
            ///
            /// # Errors
            /// Returns an error if associated [path](Path) does not start with `/dev` 
            /// or if it is not an absolute path.
            fn try_from(path: $Ty) -> ButterResult<Self> {
                Self::from_path(path)
            }
        }

    )*}
}

impl_try_from_for_devpath!{
    Component<'_>;
    Components<'_>;
    Cow<'_, OsStr>;
    &OsStr;
    OsString;
    &Path;
    PathBuf;
    &PathBuf;
    String;
    &str;
}

impl FromStr for DevPath {
    type Err = ButterError;

    /// Converts from [`str`] to [`DevPath`]
    /// 
    /// # Errors
    /// Returns an error if associated [path](Path) does not start with `/dev`
    /// or if it is not an absolute path.
    fn from_str(s: &str) -> ButterResult<Self> {
        Self::from_path(s)
    }
}

impl PartialEq<Self> for DevPath {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<P> PartialEq<P> for DevPath
where
    P: AsRef<Path>
{
    fn eq(&self, other: &P) -> bool {
        let other: &Path = other.as_ref(); 
        let path_of_self: &Path = self.0.as_ref();

        path_of_self == other
    }
}

impl PartialOrd<Self> for DevPath {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.0.partial_cmp(&other.0)
    }
}

impl<P> PartialOrd<P> for DevPath
where
    P: AsRef<Path>
{
    fn partial_cmp(&self, other: &P) -> Option<Ordering> {
        let other: &Path = other.as_ref();
        let path_of_self: &Path = self.0.as_path();
        
        path_of_self.partial_cmp(other)
    }
}

// ====================================================================================
// ------------------------------------ MOUNTPOINT ------------------------------------
// ====================================================================================

/// A wrapper around [`PathBuf`], a [`Mountpoint`] stands for the [paths](Path) which
/// a device is mounted to or *will* be mounted to. A [`Mountpoint`] has three states:
/// - [`Mounted`](Mountpoint::Mounted)
/// - [`Unmounted`](Mountpoint::Unmounted)
/// - [`UnknownStatus`](Mountpoint::UnknownStatus)
/// 
/// **NOTE**: In practice, [`UnknownStatus`](Mountpoint::UnknownStatus) should only 
/// occur when initializing a device and its corresponding [mountpoint](Mountpoint).
#[allow(clippy::missing_docs_in_private_items)]
#[derive(Debug, Clone)]
pub enum Mountpoint {
    Mounted(PathBuf),
    Unmounted(PathBuf),
    UnknownStatus(PathBuf),
}


impl Mountpoint {

    /// Parses given [path](Path) and returns a [`Mountpoint`] instance if said [path](Path)
    /// is a mountpoint.
    /// 
    /// # Errors
    /// Function will return an error if the associated path is...
    /// - non-existent
    /// - a file (in the traditional, non-UNIX manner)
    pub fn from_path(path: impl AsRef<Path>) -> ButterResult<Self> {
        let path: &Path = path.as_ref();
        path.try_into()
    }

    /// Parses given [path](Path) and returns [`Mountpoint`] instance if said [path](Path)
    /// is a mountpoint.
    /// 
    /// **NOTE:** Returns [`Mountpoint::UnknownStatus`] in the case where the checked version
    /// would result in an error.
    pub fn from_path_unchecked(path: impl AsRef<Path>) -> Self {
        let path: &Path = path.as_ref();
        
        path.try_into()
            .map_or_else(
                |_| Self::UnknownStatus(path.to_path_buf()),
                |path| path
            )
    }

    /// Returns [`Mountpoint`] associated with [`DevPath`] (e.g. /dev/sda).
    /// 
    /// # Errors
    /// Returns an error if [`DevPath`] does not have an associated [mountpoint](Mountpoint).
    pub fn from_devpath<P>(devpath: P) -> ButterResult<Self> 
    where 
        P: AsRef<Path>
    {
        let devpath = DevPath::from_path(devpath)?;
        
        match block::get_mountpoint(devpath.as_path())? {
            Some(path) => Ok(Self::Mounted(path)),
            _ => Err(ButterError::InvalidPath {
                path: devpath.0,
                reason: "cannot a mountpoint associated with devpath.".to_string()
            })
        }
    }

    /// Retrieves [`mountpoint`](Mountpoint) from device [`UUID`](Uuid)
    /// 
    /// # Errors
    /// Returns an error if [`UUID`](Uuid) is invalid.
    pub fn from_uuid(uuid: Uuid) -> ButterResult<Self> {
        let uuid_devpath = DevPath::from_uuid(uuid);

        Self::from_devpath(uuid_devpath.as_path_buf())
    }
    
    // ----- AS REFERENCE & TO FUNCTIONS ----- //
    
    /// Returns reference to [`PathBuf`]
    /// 
    /// **NOTE:** [`Mountpoint`] status will be lost and cannot be reversed.
    #[must_use]
    #[inline]
    pub const fn as_path_buf(&self) -> &PathBuf {
        match self {
            Self::Mounted(path) |
            Self::Unmounted(path) | 
            Self::UnknownStatus(path) => path,
        }
    }

    /// Returns owned [`PathBuf`]
    /// 
    /// **NOTE:** [`Mountpoint`] status will be lost and cannot be reversed.
    #[must_use]
    #[inline]
    pub fn to_path_buf(&self) -> PathBuf {
        self.as_path_buf()
            .clone()
    }

    /// Converts [`self`](Mountpoint) to [`PathBuf`]
    #[must_use]
    #[inline]
    pub fn into_path_buf(self) -> PathBuf {
        self.to_path_buf()
    }

    /// Returns a referenced [`Path`]
    #[must_use]
    #[inline]
    pub fn as_path(&self) -> &Path {
        self.as_path_buf()
            .as_path()
    }
    
}

impl PartialEq for Mountpoint {

    /// Returns `true` if `self == other` when both are referenced as a [`PathBuf`]
    fn eq(&self, other: &Self) -> bool {
        self.as_path_buf() == other.as_path_buf()
    }

}

impl PartialOrd for Mountpoint {

    /// Compares `self` versus `other` as [`PathBuf`]s.
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.as_path_buf()
            .partial_cmp(other.as_path_buf())
    }
}

impl<P> PartialEq<P> for Mountpoint 
where
    P: AsRef<Path>
{
    /// Returns `true` if `self == other` when both are referenced as a [`Path`]
    fn eq(&self, other: &P) -> bool {
        self.as_path() == other.as_ref()
    }
}

impl<P> PartialOrd<P> for Mountpoint
where
    P: AsRef<Path>
{
    /// Compares `self` versus `other` as [`Path`]s
    fn partial_cmp(&self, other: &P) -> Option<Ordering> {
        self.as_path()
            .partial_cmp(other.as_ref())
    }
}

/// Implements [`AsRef<P>`] for any type `P` which implements [`AsRef<Path>`]
///
/// **NOTE**: [`AsRef<P>`] is a bound introduced on [`PathBuf`] so that
///  `path.as_ref(): &PathBuf -> &P`
impl<P> AsRef<P> for Mountpoint 
where
    P: AsRef<Path>,
    PathBuf: AsRef<P>
{
    fn as_ref(&self) -> &P {
        self.as_path_buf()
            .as_ref()
    }
}


/// For multiple types, implements [`Into`] for [`Mountpoint`].
/// This is because a conversion from [`Mountpoint`] to a given type is guaranteed from
/// [`TryFrom`] due to how [`Mountpoint`] is structured (in particular its variants connoting
/// information about the [`Mountpoint`]'s status).
/// 
/// In other words, a conversion from [`Mountpoint`] to a given type is infalliable yet entails 
/// a loss of information about said status.
macro_rules! impl_into_for_mountpoint {

    ( $( $Ty:ty ;)* ) => {$(
        
        #[allow(clippy::from_over_into)]
        impl Into<$Ty> for Mountpoint {
        
            #[doc = concat!("Converts from [`Mountpoint`] to [`", stringify!($Ty), "`]")]
            ///
            /// **NOTE:** [`Mountpoint`] cannot implement
            #[doc = concat!("[`From<", stringify!($Ty), ">`]")]
            /// because a given [mountpoint](Mountpoint) not guaranteed to be valid.
            /// In that case, one should use a fallible conversion using [`TryFrom`].
            fn into(self) -> $Ty {
                self.as_path()
                    .into()
            }
        }

    )*}
    
}

// manually implement as many types as possible which implements AsRef<Path> in macro
impl_into_for_mountpoint! {
    OsString;
    PathBuf;
    //String;
}

/// For multiple types, this macro implements [`TryFrom`] for [`Mountpoint`]
/// 
/// **NOTE:** Keeping in mind that one cannot override the blanket implementation of
/// `TryFrom<P: AsRef<Path>>`, an explicitly enumerated [`TryFrom`] implementation becomes our
/// second best option.
macro_rules! impl_try_from_for_mountpoint {
    ( $( $Ty:ty ;)+ ) => {$(

        impl TryFrom<$Ty> for Mountpoint {
            type Error = ButterError;

            #[doc = concat!("Converts from [`", stringify!($Ty), "`] to a [`Mountpoint`].")]
            ///
            /// ## Error
            /// This conversion will result in an error if the [path](Path) associated with
            /// this type...
            /// - does not exist
            /// - is a file (in the traditional, non-UNIX sense)
            fn try_from(path: $Ty) -> ButterResult<Self> {
                let path_ref: &Path = path.as_ref();
                // in case of error
                let beginning_error_text = concat!(
                    "Path associated with ", 
                    stringify!($Ty), 
                    " is invalid for the following reasons: "
                ).to_string();
                let mut reasons: Vec<&str> = Vec::new();
                // guard clauses
                if !path_ref.exists()    { reasons.push("path does not exist"); }
                if path_ref.is_file()    { reasons.push("path is a file");      }

                if reasons.len() > 0 {
                    let reasons = (*reasons).join(", ");
                    return Err(ButterError::InvalidPath {
                        path: path_ref.to_path_buf(),
                        reason: beginning_error_text + reasons.as_str()
                    })
                }

                // finally, return mountpoint
                match block::is_mounted(&path)? {
                    true  => Ok(Mountpoint::Mounted(path_ref.to_path_buf())),
                    false => Ok(Mountpoint::Unmounted(path_ref.to_path_buf())),
                }
            }
        }

    )*}
}


// manually implement everything which implements AsRef<Path> in macro
impl_try_from_for_mountpoint!{
    Component<'_>;
    Components<'_>;
    Cow<'_, OsStr>;
    &OsStr;
    OsString;
    &Path;
    PathBuf;
    &PathBuf;
    String;
    &str;
}
