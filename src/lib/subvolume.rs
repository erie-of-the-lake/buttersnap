/*!
 * TODO: make docstring
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
use crate::{
    error::*,
    path::*,
};

use btrfs::CreateSnapshotFlags;
use derive_builder::Builder;
// external imports
use bitflags::bitflags;
use genawaiter::{
    yield_,
    rc::gen,
};
use itertools::Itertools;
use libbtrfsutil as btrfs;
use strum::{
    Display,
    //EnumProperty,
    EnumString,
};
use uuid::Uuid;

// std imports
use std::{
    cmp::Ordering,
    path::{Path, PathBuf},
    fmt::Debug,
    ops::BitOrAssign, 
    os::raw::c_int,
    time::SystemTime,
};

// ====================================================================================
// -------------------------------------- TESTS ---------------------------------------
// ====================================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use uuid::uuid;
    use std::time::Duration;


    // -----=[ PRELUDE ]=----- //


    /// Returns [SystemTime] (in secs) since the Unix Epoch
    fn seconds_since_unix_epoch(secs: u64) -> SystemTime {
        SystemTime::UNIX_EPOCH + Duration::from_secs(secs)
    }

    /// Returns tuple of mock [subvolumes](Subvolume)
    /// 
    /// - First one is the root [Subvolume].
    /// - Second is the secondary [Subvolume].
    /// - Third is an assumed snapshot/backup of the second [Subvolume].
    /// 
    /// **NOTE:** The [`mountpoint`](Mountpoint) for the third mock [Subvolume] is explicitly
    /// wrong for the sake of the tests.
    fn generate_mock_subvolumes() -> (Subvolume, Subvolume, Subvolume) {
        // mock root subvolume
        let mock_subvolume_0 = Subvolume {
            system_path_name: PathBuf::from("subv"),
            mountpoint: Mountpoint::from_path_unchecked("/"),
            id: 5,
            uuid: uuid!("0dc16371-6acc-4ead-9108-c98d5b707652"), // randomly generated
            time_created: seconds_since_unix_epoch(1_000_000_000),
            time_last_modified: seconds_since_unix_epoch(1_750_000_000),
        };

        let mock_subvolume_1 = Subvolume {
            system_path_name: PathBuf::from("subv/test"),
            mountpoint: Mountpoint::from_path_unchecked("/mnt/test"),
            id: 256,
            uuid: uuid!("fcd9ae89-c0f6-43f3-aa90-b0d6fb69c585"), // randomly generated
            time_created: seconds_since_unix_epoch(1_000_000_000),
            time_last_modified: seconds_since_unix_epoch(1_900_000_000),
        };

        // backup of `mock_subvolume_1`
        let mock_subvolume_2 = Subvolume {
            system_path_name: PathBuf::from("subv/test_snapshot"),
            mountpoint: Mountpoint::from_path_unchecked("/mnt/test"),
            id: 257,
            uuid: uuid!("d748d3ac-2d77-4f74-b8d0-cc67590fb574"), // randomly generated
            time_created: seconds_since_unix_epoch(1_200_000_000),
            time_last_modified: seconds_since_unix_epoch(1_800_000_000),
        };

        (mock_subvolume_0, mock_subvolume_1, mock_subvolume_2)
    }


    // -----=[ FUNDAMENTALS TESTS ]=----- //


    /// Tests the following functions:
    /// - [`is_older_than`]
    /// - [`is_as_old_as`]
    /// - [`is_newer_than`]
    /// 
    /// [`is_older_than`]: PartialOrdPathAndTime::is_older_than
    /// [`is_as_old_as`]: PartialOrdPathAndTime::is_as_old_as
    /// [`is_newer_than`]: PartialOrdPathAndTime::is_newer_than
    #[test]
    fn compare_time_created() {
        let (mock_subvolume_0, mock_subvolume_1, mock_subvolume_2) = generate_mock_subvolumes();
        
        assert!(mock_subvolume_1.is_older_than(&mock_subvolume_2) == Some(true));
        assert!(mock_subvolume_1.is_older_than(&mock_subvolume_0) == None);

        assert!(mock_subvolume_1.is_as_old_as(&mock_subvolume_1) == Some(true));
        assert!(mock_subvolume_1.is_as_old_as(&mock_subvolume_2) == Some(false));
        assert!(mock_subvolume_1.is_as_old_as(&mock_subvolume_0) == None);

        assert!(mock_subvolume_1.is_newer_than(&mock_subvolume_2) == Some(false));
        assert!(mock_subvolume_1.is_newer_than(&mock_subvolume_0) == None);
    }

    /// Tests the following functions:
    /// - [`less_recently_modified_than`]
    /// - [`as_recently_modified_as`]
    /// - [`more_recently_modified_than`]
    /// 
    /// [`less_recently_modified_than`]: PartialOrdPathAndTime::less_recently_modified_than
    /// [`as_recently_modified_as`]: PartialOrdPathAndTime::as_recently_modified_as
    /// [`more_recently_modified_than`]: PartialOrdPathAndTime::more_recently_modified_than
    #[test]
    fn compare_time_last_modified() {
        let (mock_subvolume_0, mock_subvolume_1, mock_subvolume_2) = generate_mock_subvolumes();

        assert!(mock_subvolume_1.less_recently_modified_than(&mock_subvolume_2) == Some(false));
        assert!(mock_subvolume_1.less_recently_modified_than(&mock_subvolume_0) == None);

        assert!(mock_subvolume_1.as_recently_modified_as(&mock_subvolume_1) == Some(true));
        assert!(mock_subvolume_1.as_recently_modified_as(&mock_subvolume_2) == Some(false));
        assert!(mock_subvolume_1.as_recently_modified_as(&mock_subvolume_0) == None);

        assert!(mock_subvolume_1.more_recently_modified_than(&mock_subvolume_2) == Some(true));
        assert!(mock_subvolume_1.more_recently_modified_than(&mock_subvolume_0) == None);
    }


    // -----=[ SNAPSHOT TESTS ]=----- //

    /*
    #[test]
    fn convert_create_snapshot_flags_to_snapshot_flags() {

    }

    #[test]
    fn convert_snapshot_flags_to_create_snapshot_flags() {

    }
    */

}

// ====================================================================================
// ----------------------------------- FUNDAMENTALS -----------------------------------
// ====================================================================================  

/// Gives a [Partial Ordering] based on:
/// - an item's [associated path]
/// - the time the item was [created]
/// - the the time the time was [last modified].
/// 
/// An [Ordering] is only guaranteed if the `self`'s and `other`'s 
/// [associated path] is the same.
/// 
/// [Partial Ordering]: PartialOrd
/// [associated path]: PartialOrdPathAndTime::associated_path
/// [created]: PartialOrdPathAndTime::time_created
/// [last modified]: PartialOrdPathAndTime::time_last_modified
trait PartialOrdPathAndTime<Rhs = Self>
where
    Rhs: ?Sized + PartialOrdPathAndTime
{
    // ----- MANDATORY FUNCTIONS ----- //

    /// Time the [`associated_path`] was created.
    /// 
    /// [`associated_path`]: PartialOrdPathAndTime::associated_path
    fn time_created(&self) -> SystemTime;

    /// Time the [`associated_path`] was last modified.
    /// 
    /// [`associated_path`]: PartialOrdPathAndTime::associated_path
    fn time_last_modified(&self) -> SystemTime;

    /// [Path] associated with the type or the instance of the type.
    fn associated_path(&self) -> &Path;

    // ----- BASIC COMPARISON FUNCTIONS ----- //

    /// Does a partial comparison of
    /// [`self.time_created()`] versus [`other.time_created()`].
    /// 
    /// Returns [`None`] if 
    /// [`self.associated_path()`] is different than [`other.associated_path()`].
    /// 
    /// The following 3 functions derive from [`partial_cmp_creation_time`]:
    /// 1. [`is_older_than`]
    /// 2. [`is_as_old_as`]
    /// 3. [`is_newer_than`]
    /// 
    /// [`self.time_created()`]: PartialOrdPathAndTime::time_created
    /// [`other.time_created()`]: PartialOrdPathAndTime::time_created
    /// 
    /// [`self.associated_path()`]: PartialOrdPathAndTime::associated_path
    /// [`other.associated_path()`]: PartialOrdPathAndTime::associated_path
    /// 
    /// [`partial_cmp_creation_time`]: PartialOrdPathAndTime::partial_cmp_creation_time
    /// [`is_older_than`]: PartialOrdPathAndTime::is_older_than
    /// [`is_as_old_as`]: PartialOrdPathAndTime::is_as_old_as
    /// [`is_newer_than`]: PartialOrdPathAndTime::is_newer_than
    fn partial_cmp_creation_time(&self, other: &Rhs) -> Option<Ordering> {
        if self.associated_path() != other.associated_path() {
            return None
        }
        self.time_created()
            .partial_cmp(&other.time_created())
    }
    
    /// Does a partial comparison of 
    /// [`self.time_last_modified()`] versus [`other.time_last_modified()`].
    /// 
    /// Returns [`None`] if
    /// [`self.associated_path()`] is different than [`other.associated_path()`].
    /// 
    /// The following 3 functions derive from [`partial_cmp_last_modified_time`]:
    /// 1. [`less_recently_modified_than`]
    /// 2. [`as_recently_modified_as`]
    /// 3. [`more_recently_modified_than`]
    /// 
    /// [`self.time_last_modified()`]: PartialOrdPathAndTime::time_last_modified
    /// [`other.time_last_modified()`]: PartialOrdPathAndTime::time_last_modified
    /// 
    /// [`self.associated_path()`]: PartialOrdPathAndTime::associated_path
    /// [`other.associated_path()`]: PartialOrdPathAndTime::associated_path
    /// 
    /// [`partial_cmp_last_modified_time`]: PartialOrdPathAndTime::partial_cmp_last_modified_time
    /// [`less_recently_modified_than`]: PartialOrdPathAndTime::less_recently_modified_than
    /// [`as_recently_modified_as`]: PartialOrdPathAndTime::as_recently_modified_as
    /// [`more_recently_modified_than`]: PartialOrdPathAndTime::more_recently_modified_than
    fn partial_cmp_last_modified_time(&self, other: &Rhs) -> Option<Ordering> {
        if self.associated_path() != other.associated_path() {
            return None
        }
        self.time_last_modified()
            .partial_cmp(&other.time_last_modified())
    }

    // ----- CREATION TIME COMPARISONS ----- //

    /// Returns `true` if and only if
    /// - `self`'s associated path is the same as `other`'s associated path.
    /// - `self` was created more recently than `other`.
    fn is_older_than(&self, other: &Rhs) -> Option<bool> {
        match self.partial_cmp_creation_time(other) {
            Some(Ordering::Less) => Some(true),
            Some(_ordering) => Some(false),
            None => None,
        }
    }

    /// Returns `true` if and only if
    /// - `self`'s associated path is the same as `other`'s associated path.
    /// - `self` was created as recently as `other`.
    fn is_as_old_as(&self, other: &Rhs) -> Option<bool> {
        match self.partial_cmp_creation_time(other) {
            Some(Ordering::Equal) => Some(true),
            Some(_ordering) => Some(false),
            None => None,
        }
    }

    /// Returns `true` if and only if
    /// - `self`'s associated path is the same as `other`'s associated path.
    /// - `self` was created at a newer time than `other`.
    fn is_newer_than(&self, other: &Rhs) -> Option<bool> {
        match self.partial_cmp_creation_time(other) {
            Some(Ordering::Greater) => Some(true),
            Some(_ordering) => Some(false),
            None => None,
        }
    }

    // ----- LAST MODIFIED TIME COMPARISONS ----- //

    /// Returns `true` if and only if
    /// - `self`'s associated path is the same as `other`'s associated path.
    /// - `self` has a more recent modified time than `other`.
    fn less_recently_modified_than(&self, other: &Rhs) -> Option<bool> {
        match self.partial_cmp_last_modified_time(other) {
            Some(Ordering::Less) => Some(true),
            Some(_ordering) => Some(false),
            None => None,
        }
    }

    /// Returns `true` if and only if
    /// - `self`'s associated path is the same as `other`'s associated path.
    /// - `self` has a last modified time equal to that of `other`.
    fn as_recently_modified_as(&self, other: &Rhs) -> Option<bool> {
        match self.partial_cmp_last_modified_time(other) {
            Some(Ordering::Equal) => Some(true),
            Some(_ordering) => Some(false),
            None => None,
        }
    }

    /// Returns `true` if and only if
    /// - `self`'s associated path is the same as `other`'s associated path.
    /// - `self` has a newer last modified time than `other`.
    fn more_recently_modified_than(&self, other: &Rhs) -> Option<bool> {
        match self.partial_cmp_last_modified_time(other) {
            Some(Ordering::Greater) => Some(true),
            Some(_ordering) => Some(false),
            None => None,
        }
    }
}


// ====================================================================================
// ------------------------------------ SUBVOLUME -------------------------------------
// ====================================================================================              

/// A [subvolume](Subvolume) is a subset of the BTRFS filesystem, each with its own
/// file/directory hierarchy which can be manipulated, copied, etc., especially
/// into snapshots, which are [subvolumes](Subvolume) of their own.
/// 
/// **NOTE:** A subvolume can only be copied if it is *not* the top-level system
/// [subvolume](Subvolume), which has a *subvolid* of 5. One can check this via 
/// `btrfs subvolume list /` with root-level privileges.
/// 
/// More detailed information on BTRFS subvolumes can be found 
/// [here](https://btrfs.readthedocs.io/en/latest/Subvolumes.html).
#[derive(Debug, Clone, Builder)]
pub struct Subvolume {
    /// Path name relative to root or top-level [subvolume](Subvolume)
    /// 
    /// E.g. If root subvolume is named `foo` and a subvolume mounted directly
    /// below with the name `bar`, its corresponding `system_path_name` would be 
    /// `foo/bar`.
    pub system_path_name: PathBuf,
    /// The [path](Path) relative to the root directory the [subvolume](Subvolume)
    /// is mounted at.
    pub mountpoint: Mountpoint,
    /// The `subvolid` of the [`Subvolume`]
    pub id: u64,
    /// The [`Subvolume`]'s [UUID](Uuid)
    pub uuid: Uuid,

    /// Time the [`Subvolume`] was created. Also known as `created` according to BTRFS API.
    pub time_created: SystemTime,
    /// Time the [`Subvolume`] was last modified. Also known as `changed` according to BTRFS API.
    pub time_last_modified: SystemTime,
}


impl Subvolume {

    /// Returns [`Subvolume`] instance whose field name and value *uniquely* corresponds
    /// to the set of all subvolumes in teh system (parsed via [`SubvolumeIterator`]). If 
    /// no such *unique* [subvolume](Subvolume) is found, then returns [`None`] instead.
    /// 
    /// # Errors
    /// If there is more than one [`Subvolume`] which corresponds to the field
    /// name and value, the function yields an error.
    fn from_fields_closure(
        field_name: &str, 
        fields_closure: impl Fn(&Self) -> bool
    ) -> ButterResult<Option<Self>>
    {
        // subvolume_iterator is of type Iterator<Item = ButterResult<Subvolume>>
        let subvolume_iterator = 
                SubvolumeIterator::from_path::<&Path>(None)?;
        let subvolumes =
                SubvolumeIterator::partition_result_and_raise_error(subvolume_iterator)?;

        let filtered_subvolumes: Vec<Self> = subvolumes
            .into_iter()
            .filter(|subvolume| fields_closure(subvolume))
            .collect();

        match filtered_subvolumes.len() {
            0 => Ok(None),
            1 => Ok(Some(filtered_subvolumes[0].clone())),
            _ => Err(ButterError::Other(
                "Multiple subvolumes found with same ".to_string() + field_name
            ))
        }
    }
    
    /// Parses the [subvolumes](Subvolume) in the BTRFS filesystem, starting at [root](ROOT),
    /// or `/`, and returns a [`Subvolume`] whose [mountpoint](Mountpoint) corresponds to 
    /// the given input mountpoint.
    /// 
    /// # Errors
    /// This function returns an error if no such [`Subvolume`] is found containing the input
    /// mountpoint.
    pub fn from_mountpoint(mountpoint: impl AsRef<Path>) -> ButterResult<Self> {

        let mountpoint = Mountpoint::from_path(mountpoint)?;
            
        Self::from_fields_closure(
            "mountpoint", 
            |subvolume| subvolume.mountpoint == mountpoint
        )?
        .ok_or_else(
            || ButterError::InvalidMountpoint(mountpoint.to_path_buf())
        )
    }

    /// Parses the [subvolumes](Subvolume) in the BTRFS filesystem, starting at [root](ROOT),
    /// or `/`, and returns a [`Subvolume`] whose `subvolid` correpsonds to the input `id`.
    /// 
    /// # Errors
    /// This function returns an error if no such [`Subvolume`] is found containing the
    /// input `id`.
    pub fn from_subvolume_id(id: u64) -> ButterResult<Self> {
        Self::from_fields_closure(
            "subvolume id",
            |subvolume| subvolume.id == id
        )?
        .ok_or_else(
            || ButterError::Other(format!(
                "Invalid subvolume ID of {id}"
            ))
        )
    }

    /// Parses the [subvolumes](Subvolume) in the BTRFS filesystem, starting at [root](ROOT),
    /// or `/`, and returns a [`Subvolume`] whose [UUID](Uuid) corresponds to the input
    /// [`uuid`](Uuid).
    /// 
    /// # Errors
    /// This function returns an error if no such [`Subvolume`] is found containing the input
    /// [`uuid`](Uuid).
    pub fn from_uuid(uuid: Uuid) -> ButterResult<Self> {
        Self::from_fields_closure(
            "UUID",
            |subvolume| subvolume.uuid == uuid
        )?
        .ok_or_else(
            || ButterError::InvalidUuid(uuid)
        )
    }
}



/// An [iterator](Iterator) which iterates through all [subvolumes](Subvolume) in a 
/// BTRFS filesystem.
#[derive(Debug)]
pub struct SubvolumeIterator;


impl SubvolumeIterator {

    /// Returns [`libbtrfsutil::SubvolumeInfoIterator`] given some [path](Path),
    /// If no [path](Path) is supplied, then defaults to [root path](ROOT).
    fn btrfs_subvolume_info_iter_from_path<P>(
        path: Option<P>
    ) -> ButterResult<btrfs::SubvolumeInfoIterator>
    where 
        P: AsRef<Path>
    {
        
        let starting_directory = path.map_or_else(
            || PathBuf::from(ROOT), 
            |path| path.as_ref().to_path_buf()
        );

        btrfs::SubvolumeInfoIterator::new(
            starting_directory, // starting path
            // Subvolume ID for root subvolume
            core::num::NonZeroU64::new(btrfs::FS_TREE_OBJECTID), // top level = 5
            btrfs::SubvolumeIteratorFlags::all(), // flags
        ).map_err(Into::into) // libbtrfsutil::Error -> ButterError::BtrfsError
    }

    /// Creates an [iterator](Iterator) of [subvolumes](Subvolume) relative to
    /// `starting_directory`. If `starting_directory` is [`None`], then `starting_directory`
    /// defaults the [root directory](ROOT), or `/`.
    /// 
    /// # Errors
    /// This function will return an error if...
    /// - the BTRFS API fails to initiate an iterator.
    /// - a yielded [`Subvolume`] contains an invalid [`Mountpoint`]
    pub fn from_path<P>(
        starting_directory: Option<P>
    ) -> ButterResult<impl Iterator<Item = ButterResult<Subvolume>>>
    where
        P: AsRef<Path> // <- need to use turbofish operator lest compiler error
    {
        let subvolume_info_iter: btrfs::SubvolumeInfoIterator = 
                Self::btrfs_subvolume_info_iter_from_path(starting_directory)?;
        
        // create generator akin to that in python
        // translates btrfs::SubvolumeInfoIterator to custom Iterator
        let subvolume_iterator = gen!({
            for subvolume_info_result in subvolume_info_iter {
                // need to propogate and yield errors manually in generator.
                // hence somewhat verbose if-let Err(error) guard clauses.
                //
                // NOTE: subvolume_info_result is of type 
                //       Result<(PathBuf, SubvolumeInfo), libbtrfsutil::Error>
                if let Err(error) = subvolume_info_result {
                    // libbtrfsutil::Error -> ButterError::BtrfsError
                    yield_!( Err(error.into()) );
                    break
                }
                // safe to unwrap
                let (system_path_name, subvolume_info): (PathBuf, btrfs::SubvolumeInfo) =
                        subvolume_info_result.unwrap();

                let mountpoint: ButterResult<Mountpoint> = 
                        Mountpoint::from_uuid(subvolume_info.uuid());
                if let Err(mountpoint_error) = mountpoint {
                    yield_!(Err(mountpoint_error));
                    break
                }
                let mountpoint: Mountpoint = mountpoint.unwrap(); // safe to unwrap

                let subvolume_parent_id: Option<u64> = match subvolume_info.parent_id() {
                    // Convert NonZeroU64 to u64 via `get()`
                    Some(number) => Some(number.get()),
                    None => None,
                };
                // finally, construct and yield Subvolume instance
                yield_!(Ok(Subvolume {
                    system_path_name:   system_path_name,
                    mountpoint:         mountpoint,
                    id:                 subvolume_info.id(),
                    uuid:               subvolume_info.uuid(),

                    time_created:       subvolume_info.created(),
                    time_last_modified: subvolume_info.changed(),
                }));
            }
        }).into_iter();

        Ok(subvolume_iterator)
    }

    /// Parses an [iterator](Iterator) whose [items](Iterator::Item) contain
    /// `ButterResult<Subvolume>`, and returns the [`Subvolume`]s as a [vector](Vec)
    /// only if no [error](ButterError) is encountered in the [iterator](Iterator).
    /// 
    /// **NOTE:** Uses [`Itertools`]'s [`partition_result`](Itertools::partition_result)
    /// function to separate [`Ok`]s and [`Err`]s
    fn partition_result_and_raise_error<I>(items: I) -> ButterResult<Vec<Subvolume>> 
    where
        I: Iterator<Item = ButterResult<Subvolume>>
    {
        let (subvolumes, errors): (Vec<Subvolume>, Vec<ButterError>) =
                items.partition_result();

        // only need to return first error, if any
        if let Some(error) = errors.into_iter().next() { return Err(error) }
    
        Ok(subvolumes)
    }
}

impl PartialEq for Subvolume {
    /// Returns `true` if and only if [`self.uuid`](Subvolume) is equal to 
    /// [`other.uuid`](Subvolume).
    fn eq(&self, other: &Self) -> bool {
        self.uuid == other.uuid
    }
}

impl PartialOrdPathAndTime for Subvolume {

    /// Returns `self.time_created`.
    fn time_created(&self) -> SystemTime { 
        self.time_created 
    }

    /// Returns `self.time_last_modified`.
    fn time_last_modified(&self) -> SystemTime {
        self.time_last_modified
    }

    /// Returns `self.mountpoint`.
    fn associated_path(&self) -> &Path {
        self.mountpoint.as_path()
    }
}

// ====================================================================================
// ------------------------------------- SNAPSHOTS ------------------------------------
// ====================================================================================

/// [Snapshots](Snapshot) are special types of [subvolumes](Subvolume) which, although
/// may not be actively used, carry the content of the original [subvolume](Subvolume)
/// they snapshotted.
/// 
/// In the context of the `buttersnap` program, [`Snapshot`]s also contain additional
/// [metadata](SnapshotMetadata) attached such as [comments](Comment) and [tags](Tag).
/// 
/// For more information on BTRFS [snapshots](Snapshot),
/// see [here](https://btrfs.readthedocs.io/en/latest/btrfs-subvolume.html#subvolume-and-snapshot)
#[derive(Debug, Clone, Builder)]
pub struct Snapshot {
    
    /// Directory, or [folder path](Path), the [snapshot](Snapshot) is backing up
    pub associated_backup_directory: PathBuf,

    /// The subvolume associated with the snapshot
    pub subvolume: Subvolume,

    /// Current [mountpoint](Mountpoint) of the [snapshot](Snapshot).
    /// 
    /// **NOTE:** [`self.mountpoint`](Mountpoint) is equal to 
    /// [`self.subvolume.mountpoint`](Mountpoint)
    pub mountpoint: Mountpoint,

    /// [UUID](Uuid) of the [snapshot](Snapshot).
    /// 
    /// **NOTE:** [`self.uuid`](Uuid) is equal to [`self.subvolume.uuid`](Uuid)
    pub uuid: Uuid,

    /// Optional [metadata](SnapshotMetadata) for the [`Snapshot`]
    pub metadata: Option<SnapshotMetadata>,
}

impl Snapshot {

    #[allow(clippy::doc_markdown)]
    /// Creates a bare [`Snapshot`] without any [tags](Tag) or [comments](Comment)
    /// given an original [`Subvolume`] (to be snapshotted) and the location or directory
    /// - i.e. [`Mountpoint`] - the [`Snapshot`] is to be located.
    /// 
    /// [`SnapshotFlags`] are a set of flags able to consist of any combination
    /// (or lack thereof) of the following flags:
    /// - [`READ_ONLY`](SnapshotFlags::READ_ONLY)
    /// - [`RECURSIVE`](SnapshotFlags::RECURSIVE)
    /// For passing in zero flag arguments, use the [`SnapshotFlags::empty()`] or
    /// [`SnapshotFlags::new()`] method.
    /// 
    /// See [`SnapshotFlags`] for more technical information on its flags.
    /// 
    /// **NOTE:** For clarification, `snapshot_location` is the 
    /// [`Snapshot`]'s associated [mountpoint](Mountpoint).
    /// 
    /// **NOTE 2:** This function intentionally does not take into account
    /// Subvolume [Quota Groups], or QGroups.
    /// 
    /// # Errors
    /// This function may return an error if...
    /// - The flags (more technically the bitfield associated with the flags) are improperly
    /// instantiated
    /// - The [`Snapshot`] creation process fails.
    /// - `snapshot_location` points to an invalid [`Mountpoint`]
    /// 
    /// [Quota Groups]: https://man7.org/linux/man-pages/man8/btrfs-quota.8.html
    pub fn create_snapshot(
        original_subvolume: &Subvolume,
        snapshot_location: &impl AsRef<Path>,
        flags: SnapshotFlags,
    ) -> ButterResult<Self> {
        // TODO: account for RECURSIVE flag
        //       this probably requires refactoring using libbtrfsutil_sys
        let flags: CreateSnapshotFlags = flags.try_into()?;

        btrfs::create_snapshot(
            original_subvolume.mountpoint.as_path(),
            snapshot_location,
            flags, // can safely unwrap due to above
            None,
        )?;

        let snapshot_subvolume = Subvolume::from_mountpoint(snapshot_location)?;
        let snapshot_uuid = snapshot_subvolume.uuid;
        let snapshot_mountpoint = snapshot_subvolume.clone().mountpoint;
        
        SnapshotBuilder::default()
            .associated_backup_directory(original_subvolume.mountpoint.to_path_buf())
            .mountpoint(snapshot_mountpoint)
            .subvolume(snapshot_subvolume)
            .uuid(snapshot_uuid)
            .build()
            .map_err(|err| ButterError::Other(err.to_string()))
    }

    #[allow(clippy::doc_markdown)]
    /// Creates a bare [`Snapshot`] without any [tags](Tag) or [comments](Comment)
    /// given the [`Subvolume`]'s [mountpoint](Mountpoint) and the location or directory -
    /// i.e. [`Mountpoint`] - the [`Snapshot`] is to be located.
    /// 
    /// [`SnapshotFlags`] are a set of flags able to consist of any combination
    /// (or lack thereof) of the following flags:
    /// - [`READ_ONLY`](SnapshotFlags::READ_ONLY)
    /// - [`RECURSIVE`](SnapshotFlags::RECURSIVE)
    /// For passing in zero flag arguments, use the [`SnapshotFlags::empty()`] or
    /// [`SnapshotFlags::new()`] method.
    /// 
    /// See [`SnapshotFlags`] for more technical information on its flags.
    /// 
    /// **NOTE:** For clarification, `snapshot_location` is the 
    /// [`Snapshot`]'s associated [mountpoint](Mountpoint).
    /// 
    /// **NOTE 2:** This function intentionally does not take into account
    /// Subvolume [Quota Groups], or QGroups.
    /// 
    /// # Errors
    /// This function may return an error if...
    /// - The flags (more technically the bitfield associated with the flags) are improperly
    /// instantiated
    /// - The [`Snapshot`] creation process fails.
    /// - `snapshot_location` points to an invalid [`Mountpoint`]
    /// 
    /// [Quota Groups]: https://man7.org/linux/man-pages/man8/btrfs-quota.8.html
    pub fn create_snapshot_from_path<P, Q>(
        subvolume_mountpoint: P,
        snapshot_location: Q,
        flags: SnapshotFlags
    ) -> ButterResult<Self>
    where
        P: AsRef<Path>,
        Q: AsRef<Path>
    {
        // TODO: account for RECURSIVE flag
        //       this probably requires refactoring using crate libbtrfsutil_sys
        let flags: CreateSnapshotFlags = flags.try_into()?;

        btrfs::create_snapshot(
            &subvolume_mountpoint,
            &snapshot_location,
            flags,
            None,
        )?;

        let subvolume_mountpoint: PathBuf = subvolume_mountpoint.as_ref().to_path_buf();
        let snapshot_subvolume = Subvolume::from_mountpoint(snapshot_location)?;

        SnapshotBuilder::default()
            .associated_backup_directory(subvolume_mountpoint)
            .mountpoint(snapshot_subvolume.clone().mountpoint)
            .subvolume(snapshot_subvolume.clone())
            .uuid(snapshot_subvolume.uuid)
            .build()
            .map_err(|err| ButterError::Other(err.to_string()))
    }


    // ---- SNAPSHOT METADATA METHODS ---- //

    /// Returns tags, i.e. [`Vec<Tag>`], if the following are true...
    /// 1. [`self.metadata`](SnapshotMetadata) is [`Some`].
    /// 2. [`self.metadata.tags`](Tag) is [`Some`].
    /// 
    /// Returns [`None`] otherwise.
    pub fn tags(&self) -> Option<Vec<Tag>> {
        let Some(metadata) = &self.metadata else {
            return None
        };
        metadata.tags.clone()
    }

    /// Returns comments, i.e. [`Vec<Comment>`], if the following are true...
    /// 1. [`self.metadata`](SnapshotMetadata) is [`Some`].
    /// 2. [`self.metadata.comments`](SnapshotMetadata) is [`Some`].
    /// 
    /// Returns [`None`] otherwise.
    pub fn comments(&self) -> Option<Vec<Comment>> {
        let Some(metadata) = &self.metadata else {
            return None
        };
        metadata.comments.clone()
    }
}

impl PartialOrdPathAndTime for Snapshot {
    
    /// Returns when [`self.subvolume`](Subvolume) was created.
    fn time_created(&self) -> SystemTime {
        self.subvolume.time_created
    }

    /// Returns when [`self.subvolume`](Subvolume) was last modified.
    fn time_last_modified(&self) -> SystemTime {
        self.subvolume.time_last_modified
    }

    /// Returns the backup directory the [`Snapshot`] shadows.
    fn associated_path(&self) -> &Path {
        &self.associated_backup_directory
    }

}

impl PartialOrdPathAndTime<Subvolume> for Snapshot {

    /// Returns when [`self.subvolume`](Subvolume) was created.
    fn time_created(&self) -> SystemTime {
        self.subvolume.time_created
    }

    /// Returns when [`self.subvolume`](Subvolume) was last modified.
    fn time_last_modified(&self) -> SystemTime {
        self.subvolume.time_last_modified
    }

    /// Returns the backup directory the [`Snapshot`] shadows.
    fn associated_path(&self) -> &Path {
        &self.associated_backup_directory
    }
    
}


bitflags!{
    /// Flags for creating [`Snapshots`](Snapshot).
    /// 
    /// In technical terms, [`SnapshotFlags`] is a [bitfield] able to contain any combination
    /// of the following flags:
    /// - [`READ_ONLY`](SnapshotFlags::READ_ONLY)
    /// - [`RECURSIVE`](SnapshotFlags::RECURSIVE)
    /// Each flag in [`SnapshotFlags`] is represented as an [`i32`]
    /// 
    /// [bitfield]: https://docs.rs/buttersnap/0.1.0/buttersnap/subvolume/struct.Snapshot.html 
    pub struct SnapshotFlags: i32 {
        /// When taking a BTRFS snapshot, this sets the resulting [snapshot](Snapshot) to read-only.
        const READ_ONLY = btrfs::CreateSnapshotFlags::READ_ONLY.bits();

        /// When taking a BTRFS snapshot, this recursively takes a [snapshot](Snapshot) of 
        /// any extra [subvolumes](Subvolume) residing beneath the [subvolume](Subvolume)
        /// being snapshotted.
        const RECURSIVE = btrfs::CreateSnapshotFlags::RECURSIVE.bits();
    }
}

impl SnapshotFlags {

    /// Creates [`SnapshotFlags`] bitfield containing zero enabled flags.
    #[must_use]
    pub const fn new() -> Self {
        Self::empty()
    }

    /// Enables `READ_ONLY` flag in [`SnapshotFlags`]
    /// 
    /// # Panics
    /// This function panics if `READ_ONLY` flag is already set. E.g.,
    /// ```should_panic
    /// # use buttersnap::subvolume::SnapshotFlags;
    /// let snapshot_flags = SnapshotFlags::new()
    ///     .read_only()
    ///     .read_only();
    /// ```
    #[must_use]
    #[inline]
    pub fn read_only(mut self) -> Self {
        assert!(
            !self.contains(Self::READ_ONLY),
            "READ_ONLY flag already set for {self:#?}"
        );
        self.bitor_assign(Self::READ_ONLY);
        self
    }

    /// Enables `RECURSIVE` flag in [`SnapshotFlags`]
    /// 
    /// # Panics
    /// This function panics if the `RECURSIVE` flag is already set. E.g.,
    /// ```should_panic
    /// # use buttersnap::subvolume::SnapshotFlags;
    /// let snapshot_flags = SnapshotFlags::new()
    ///     .recursive()
    ///     .recursive();
    /// ```
    #[must_use]
    #[inline]
    pub fn recursive(mut self) -> Self {
        assert!(
            !self.contains(Self::RECURSIVE),
            "RECURSIVE flag already set for {self:#?}"
        );
        self.bitor_assign(Self::RECURSIVE);
        self
    }
}

impl TryFrom<CreateSnapshotFlags> for SnapshotFlags {
    type Error = ButterError;

    fn try_from(flags: CreateSnapshotFlags) -> Result<Self, ButterError> {
        let flags: i32 = flags.bits();

        Self::from_bits(flags)
            .ok_or_else(|| ButterError::Other([
                "Flags do not have correct bit values in order to make SnapshotFlags.",
                format!("Flags have value of... {flags:#?}").as_str()
            ].join("\n")))
    }
}

impl TryFrom<SnapshotFlags> for CreateSnapshotFlags {
    type Error = ButterError;

    fn try_from(flags: SnapshotFlags) -> Result<Self, ButterError> {
        let flags: c_int = flags.bits();
        
        Self::from_bits(flags)
            .ok_or_else(|| ButterError::Other([
                "Flags do not have correct bit values in order to make CreateSnapshotFlags.",
                format!("Flags have value of... {flags:#?}").as_str()
            ].join("\n")))
    }
}

// ====================================================================================
// --------------------------------- SNAPSHOT METADATA --------------------------------
// ====================================================================================

/// Metadata to describe how or why a particular [`Snapshot`] was formed.
#[derive(Debug, Clone)]
pub struct SnapshotMetadata {
    /// [Tag(s)](Tag) passed in either manually from the user or automatically
    /// from the `buttersnap` daemon.
    /// 
    /// Acts as a type of metadata to tell the program (or user) how this [snapshot](Snapshot)
    /// was formed.
    pub tags: Option<Vec<Tag>>,

    /// [Comment(s)](Comment) passed in during the creation of the
    /// [snapshot](Snapshot)
    /// 
    /// Acts as a type of metadata to tell the user why the associated
    /// [snapshot](Snapshot) was taken.
    pub comments: Option<Vec<Comment>>,
}

impl SnapshotMetadata {

    /// Adds a selection of [tag(s)](Tag) to `self.tags`.
    /// If `self.tags` is [`None`], then it gets turned into the [`Some`] variety.
    pub fn add_tags(&mut self, mut tags: Vec<Tag>) -> &mut Self {
        if tags.is_empty() { return self }

        let mut current_tags = match &self.tags {
            Some(t) => t.to_vec(),
            None => Vec::new(),
        };
        current_tags.append(&mut tags);
        
        self.tags = Some(current_tags.to_vec());
        self
    }

    /// Adds a selection of unique [tag(s)](Tag) to `self.tags`. In other words, if a [Tag]
    /// already exists in `self.tags`, then said [Tag] will not be added.
    /// 
    /// If `self.tags` is [`None`], then it gets turned into the [`Some`] variety.
    pub fn add_unique_tags(&mut self, mut tags: Vec<Tag>) -> &mut Self {
        if tags.is_empty() { return self }

        let mut current_tags: Vec<Tag> = match &self.tags {
            Some(t) => t.to_vec(),
            None => Vec::new(),
        };
        current_tags.append(&mut tags); // returns `()`, so chaining doesn't work
        current_tags.dedup(); // same as above
       
        self.tags = Some(current_tags);
        self
    }

    /// Adds a selection of [comment(s)](Comment) to `self.comment`.
    /// If `self.comments` is [`None`], then it gets turned into the [`Some`] variety.
    pub fn add_comments(&mut self, mut comments: Vec<Comment>) -> &mut Self {
        if comments.is_empty() { return self }
        
        let mut current_comments: Vec<Comment> = match &self.comments {
            Some(t) => t.to_vec(),
            None => Vec::new(),
        };
        current_comments.append(&mut comments);

        self.comments = Some(current_comments);
        self
    }
}

/// A type of metadata for to tell the `buttersnap` program how a [`Snapshot`]
/// was formed.
/// 
/// # Notable [`Tag`] Properties
/// 
/// [`Tag`] implements the [`FromStr`](std::str::FromStr) `trait` as a getter for its
/// variants, all in an ascii-case-insensitive manner. Furthermore, one can get a
/// variant through either its full spelling or its first letter.
/// Altogether, for one variant - say, [`Tag::Update`] - the following (non-exhaustive) 
/// cases are true:
/// ```rust
/// # use buttersnap::error::ButterResult;
/// #
/// # fn main() -> Result<(), strum::ParseError> {
/// # use buttersnap::subvolume::Tag;
/// # use std::str::FromStr;
/// // full spelling
/// assert_eq!(Tag::from_str("Update"), Ok(Tag::Update));
/// assert_eq!(Tag::from_str("UpDatE"), Ok(Tag::Update));
/// assert_eq!(Tag::from_str("update"), Ok(Tag::Update));
/// // first letter
/// assert_eq!(Tag::from_str("U"), Ok(Tag::Update));
/// assert_eq!(Tag::from_str("u"), Ok(Tag::Update));
/// #
/// # Ok(())
/// # }
/// ```
/// 
/// Additionally, [`Tag`] variants implement the [`ToString`] `trait`
/// by returning the variant's first letter capitalized.
/// For instance, with the variant [`Tag::Monthly`],
/// ```rust
/// # use buttersnap::subvolume::Tag;
/// assert_eq!("M".to_string(), Tag::Monthly.to_string());
/// ```
#[derive(Debug, Clone, PartialEq, Eq, EnumString, Display)]
#[strum(ascii_case_insensitive)]
pub enum Tag {
     
    /// [`Tag`] typically indicating a [snapshot](Snapshot) was taken manually.
    #[strum(serialize = "O", serialize = "Other"  , to_string = "O")]
    Other,

    /// [`Tag`] indicating a [snapshot](Snapshot) was taken at boot.
    #[strum(serialize = "B", serialize = "Boot"   , to_string = "B")]
    Boot,

    /// [`Tag`] indicating a [snapshot](Snapshot) was taken just before or after a system update.
    #[strum(serialize = "U", serialize = "Update" , to_string = "U")]
    Update,

    /// [`Tag`] indicating a [snapshot](Snapshot) was taken during an hourly
    /// or semi-hourly backup.
    #[strum(serialize = "H", serialize = "Hourly" , to_string = "H")]
    Hourly,

    /// [`Tag`] indicating a [snapshot](Snapshot) was taken during a daily
    /// or semi-daily backup.
    #[strum(serialize = "D", serialize = "Daily"  , to_string = "D")]
    Daily,

    /// [`Tag`] indicating a [snapshot](Snapshot) was taken during a weekly
    /// or semi-weekly backup.
    #[strum(serialize = "W", serialize = "Weekly" , to_string = "W")]
    Weekly,

    /// [`Tag`] indicating a [snapshot](Snapshot) was taken during a monthly
    /// or semi-monthly backup.
    #[strum(serialize = "M", serialize = "Monthly", to_string = "M")]
    Monthly,
}

/// A [`String`] containing the description of an associated [`Snapshot`].
/// This also acts as a special-case thin wrapper around [`String`].
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Comment(String);