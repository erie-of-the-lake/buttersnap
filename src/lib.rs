/*! 
TODO: make docstring for program
!*/

// =====================
// ------ IMPORTS ------
// =====================

// EXTERNAL IMPORTS 



// block_utils
use block_utils as block;
use block::BlockUtilsError;
// derive_builder
use derive_builder::Builder;
// fields_iter
// NOTE: allows for iterating over fields_struct
use fields_iter::{
    FieldsIter,
    FieldsIterMut,
    FieldsInspect,
};
// genawaiter
use genawaiter::{
    yield_,
    rc::gen,
};
// libbtrfsutil
use libbtrfsutil as btrfs;
use btrfs::{
    SubvolumeInfo          as SubvInfo,
    SubvolumeInfoIterator  as SubvInfoIter,
    SubvolumeIterator      as SubvIter,
    SubvolumeIteratorFlags as SubvIterFlags,
};
// sealed
use sealed::sealed;
// serde
use serde::{
    Serialize, Deserialize,
    Serializer, Deserializer,
    ser::{SerializeMap, SerializeStruct},
};
// strum
use strum;
use strum_macros::{
    EnumProperty,
    EnumString,
    Display,
};
// uuid
use uuid::Uuid;
// thiserror
use thiserror::Error;

// ----- STD IMPORTS -----
use std::{
    cmp::Ordering,
    collections::HashMap,
    ffi   ::{OsStr, OsString},
    marker::{Send, Sync},
    ops   ::Deref,
    path  ::{Path, PathBuf},
    time  ::SystemTime,
};




// ====================================================================================
// --------------------------- FUNDAMENTALS & ERROR PARSING ---------------------------
// ====================================================================================

type ButterResult<T> = Result<T, ButterError>;

#[derive(Debug, Error)]
pub enum ButterError {

    // =========================== //
    // ----- EXTERNAL ERRORS ----- //
    // =========================== //

    #[error(transparent)]
    BlockUtilsError(BlockUtilsError),

    #[error(transparent)]
    BtrfsError(btrfs::Error),

    #[error(transparent)]
    UuidParseError(uuid::Error),

    // =========================== //
    // ----- INTERNAL ERRORS ----- //
    // =========================== //


    // ----- Path-Related Errors ----- //

    // Generic path error
    #[error("Invalid path of `{}` : {}", 
            path.to_string_lossy(), 
            reason)]
    InvalidPath {
        path: PathBuf,
        reason: String,
    },

    // ----- Devpath-Related Errors ----- //

    #[error("Invalid path at `/dev` : `{}` does not exist", 
            .0.display() )]
    InvalidDevpath(PathBuf),
    
    #[error("Invalid path at `/dev` : `{}` does not have a parent path", 
            .0.display() )]
    InvalidParentDevpath(PathBuf),

    // ----- Mountpoint-Related Errors ----- //
    
    #[error("Invalid mountpoint : '{}' is not recognized", 
            .0.to_string_lossy() )]
    InvalidMountpoint(PathBuf),

    #[error("Invalid path : cannot find a mountpoint associated with `{}`",
            .0.to_string_lossy() )]
    InvalidPathForMountpoint(PathBuf),

    // ----- Device-Related & UUID-Related Errors ----- //

    #[error("Invalid UUID : '{}' does not exist", 
            .0.hyphenated().to_string() )]
    InvalidUuid(Uuid), 

    #[error("Device `{}` does not have a UUID",
            .0.to_string_lossy() )]
    NonexistentUUID(PathBuf),

    // ----- Misc. Errors ----- //

    #[error("{0}")]
    Other(String),

}

// NOTE: may need to make macro for implementing
// `impl From<Error> to ButterError` boilerplatecd

macro_rules! impl_from_error_for_butter_error {
    ( $external_error:ty, $butter_error_plus_variant:expr ) => {

        impl From<$external_error> for ButterError {
            fn from(error: $external_error) -> Self {
                $butter_error_plus_variant(error)
            }
        }
    // end impl
    }
}

impl_from_error_for_butter_error!(BlockUtilsError, ButterError::BlockUtilsError);
impl_from_error_for_butter_error!(btrfs::Error   , ButterError::BtrfsError     );
impl_from_error_for_butter_error!(uuid::Error    , ButterError::UuidParseError );


// ----- NON-METHOD FUNCTIONS ----- //

pub const OS_SEPARATOR: &str = "/";
pub const ROOT: &str = &OS_SEPARATOR;
pub const DEV_DISK_BYUUID: &str = "/dev/disk/by-uuid"; 

// ----- TRAITS ----- //


trait PartialOrdPathAndTime<Rhs = Self>:
where
    Rhs: ?Sized + PartialOrdPathAndTime
{
    fn time_created(&self) -> SystemTime;
    fn time_last_modified(&self) -> SystemTime;
    fn associated_path(&self) -> &Path;

    fn partial_cmp_creation_time(&self, other: &Rhs) -> Option<Ordering> {
        if self.associated_path() != other.associated_path() {
            return None
        }
        self.time_created()
            .partial_cmp( &other.time_created() )
    }

    fn partial_cmp_last_modified_time(&self, other: &Rhs) -> Option<Ordering> {
        if self.associated_path() != other.associated_path() {
            return None
        }
        self.time_last_modified()
            .partial_cmp( &other.time_last_modified() )
    }

    // ----- CREATION TIME COMPARISONS ----- //

    fn is_older_than(&self, other: &Rhs) -> Option<bool> {
        match self.partial_cmp_creation_time(other) {
            Some(Ordering::Less) => Some(true),
            Some(_ordering) => Some(false),
            None => None,
        }
    }

    fn is_as_old_as(&self, other: &Rhs) -> Option<bool> {
        match self.partial_cmp_creation_time(other) {
            Some(Ordering::Equal) => Some(true),
            Some(_ordering) => Some(false),
            None => None,
        }
    }

    fn is_newer_than(&self, other: &Rhs) -> Option<bool> {
        match self.partial_cmp_creation_time(other) {
            Some(Ordering::Greater) => Some(true),
            Some(_ordering) => Some(false),
            None => None,
        }
    }

    // ----- LAST MODIFIED TIME COMPARISONS ----- //

    fn less_recently_modified_than(&self, other: &Rhs) -> Option<bool> {
        match self.partial_cmp_last_modified_time(other) {
            Some(Ordering::Less) => Some(true),
            Some(_ordering) => Some(false),
            None => None,
        }
    }

    fn as_recently_modified_as(&self, other: &Rhs) -> Option<bool> {
        match self.partial_cmp_last_modified_time(other) {
            Some(Ordering::Equal) => Some(true),
            Some(_ordering) => Some(false),
            None => None,
        }
    }

    fn more_recently_modified_than(&self, other: &Rhs) -> Option<bool> {
        match self.partial_cmp_last_modified_time(other) {
            Some(Ordering::Greater) => Some(true),
            Some(_ordering) => Some(false),
            None => None,
        }
    }

}


macro_rules! pathbuf {
    // 0 args
    ( [] ) => ( Pathbuf::new() );
    // 1 arg
    ( $path_slice:expr ) => ( PathBuf::from($path_slice) );
    // > 1 args
    // "/" as joiner since program is incompatible with Windows by nature
    ( $( $path_slice:expr ),+ ) => {
        PathBuf::from( [ $( $path_slice ),* ].join(OS_SEPARATOR) )
    };
}

/// Translates [`UUID`](Uuid) to a path located in `/dev`. 
///     - If `get_parent_devpath` is false, then defaults to returning 
/// `/dev/disk/by-uuid/01234567-89ab-cdef-0123456789ab` as an example.
///     - Otherwise, if `get_parent_devpath` is true, then it returns the like of
/// `/dev/sdX`, `/dev/nvme0nX`, `/dev/mmcblkX`, etc.
pub fn get_devpath_from_uuid(uuid: Uuid, get_parent_devpath: bool) -> ButterResult<PathBuf> {
    //let dev_disk_byuuid = "/dev/disk/by-uuid";
    let uuid_string = uuid.hyphenated().to_string();
    let uuid_str = uuid_string.as_str();
    let uuid_devpath = pathbuf![DEV_DISK_BYUUID, uuid_str];

    let error = ButterError::InvalidDevpath(uuid_devpath.clone());
    // guard clauses
    if !uuid_devpath.exists() { return Err(error) }
    if !get_parent_devpath    { return Ok(uuid_devpath) }

    block::get_parent_devpath_from_path(&uuid_devpath)?
        .ok_or_else(|| ButterError::InvalidParentDevpath(uuid_devpath) )

}


// ====================================================================================
// ------------------------------------ MOUNTPOINT ------------------------------------
// ====================================================================================


#[derive(Debug, Clone, Eq)]
pub enum Mountpoint {
    Mounted(PathBuf),
    Unmounted(PathBuf),
    UnknownStatus(PathBuf),
}

impl Mountpoint {
    
    /// Returns default instance of [`Mountpoint`]
    /// i.e. `Mountpoint::UnknownStatus(PathBuf::new())`
    pub fn new() -> Self {
        Self::default()
    }

    /// Parses given path to see if it is a mountpoint and returns a [`Mountpoint`]
    /// instance correspondingly.
    /// 
    /// **NOTE:** If the path given is not a mountpoint, it will return
    /// `Mountpoint::UnknownStatus(/path/to/given_path)`
    pub fn from_path<P: AsRef<Path>>(path: P) -> Self {

        let pathbuf = path.as_ref().to_path_buf();
        
        Self::from(pathbuf)
    }

    /// Returns [`Mountpoint`] associated with device in `/dev/path/to/device`
    /// (e.g. `/dev/sda`).
    /// Returns error if no such mountpoint exists.
    pub fn from_devpath<P: AsRef<Path>>(devpath: P) -> ButterResult<Self> {
        
        match block::get_mountpoint(&devpath)? {
            Some(path) => Ok(Self::Mounted(path)),
            _ => {
                let pathbuf = devpath.as_ref().to_path_buf();
                return Err(ButterError::InvalidPathForMountpoint(pathbuf))
            },
        }
    }

    /// Gets [`mountpoint`](Mountpoint) from a device [`UUID`](Uuid).
    pub fn from_uuid(uuid: Uuid) -> ButterResult<Self> {
        let uuid_devpath = get_devpath_from_uuid(uuid, false)?;
        // parse constructed devpath through `from_devpath`
        Self::from_devpath(uuid_devpath)
    }

    // ----- REFERENCE BOILERPLATE ----- //
    
    /// Returns reference to [`Path`] slice associated with [`Mountpoint`] instance
    pub fn as_path(&self) -> &Path {
        let pathbuf: &PathBuf = &**self;  // **self = &Self -> PathBuf
        pathbuf.as_path()
    }

    /// Returns [`PathBuf`] reference associated with [`Mountpoint`] instance
    pub fn as_path_buf(&self) -> &PathBuf {
        // **self = &Self -> PathBuf
        &(**self)
    }

    /// Returns [`OsStr`] reference associated with [`Mountpoint`] instance
    pub fn as_os_str(&self) -> &OsStr {
        let pathbuf: &PathBuf = &(**self);  // **self = &Self -> PathBuf
        pathbuf.as_os_str()
    }

    // ----- TYPE-CHANGING ----- //
    
    /// Returns owned [`PathBuf`] slice associated with [`Mountpoint`] instance
    pub fn to_path_buf(&self) -> PathBuf {
        // need to borrow b/c PathBuf doesn't implement copy trait
        let pathbuf: &PathBuf = &(**self);
        pathbuf.to_owned()
    }
    
    /// Returns owned [`OsString`] slice associated with [`Mountpoint`] instance
    pub fn to_os_string(&self) -> OsString {
        let os_str: &OsStr = self.as_os_str();
        os_str.to_os_string()
    }


}

impl Default for Mountpoint {
    fn default() -> Self {
        Self::UnknownStatus(PathBuf::new())
    }
}

impl PartialEq for Mountpoint {

    /// Returns `true` if and only if [`PathBuf`] associated with `self` is equal
    /// to [`PathBuf`] with `other`.
    fn eq(&self, other: &Self) -> bool {
        self.as_path_buf() == other.as_path_buf()
    }

    fn ne(&self, other: &Self) -> bool {
        self.as_path_buf() != other.as_path_buf()
    }

}

impl<P> From<P> for Mountpoint
    where P: AsRef<Path> {

    fn from(path: P) -> Self {
        let pathbuf = path.as_ref().to_path_buf();
        match block::is_mounted(path) {
            Ok(true)  => Self::Mounted(pathbuf),
            Ok(false) => Self::Unmounted(pathbuf),
            Err(_error) => Self::UnknownStatus(pathbuf),
        }
    }
}

impl Deref for Mountpoint {
    type Target = PathBuf;

    fn deref(&self) -> &PathBuf {
        match self {
            Self::Mounted(pathbuf)       => pathbuf,
            Self::Unmounted(pathbuf)     => pathbuf,
            Self::UnknownStatus(pathbuf) => pathbuf,
        }
    }
}

/// NOTE: `PathBuf: AsRef<P>` is a restriction places on [`PathBuf`]
/// so as to eventually make `as_ref()` eventually return `&P`
impl<P> AsRef<P> for Mountpoint
where 
    P: AsRef<Path>, 
    PathBuf: AsRef<P>,
{

    fn as_ref(&self) -> &P {
        // Operations in order:
        //  - *self  = &Self -> Self
        //  - **self = &Self -> PathBuf
        //  - pathbuf.as_ref() = PathBuf -> &P
        (**self).as_ref()
    }
}


// ====================================================================================
// ------------------------------------ SUBVOLUME -------------------------------------
// ====================================================================================


#[derive(Debug, Clone, Eq, FieldsInspect)]
pub struct Subvolume {
    /// Path name relative to root subvolume.
    /// E.g. if root subvolume is named "foo" and subvolume is named "bar" and is mounted
    /// right below the root subvolume, `system_path_name` would be *"foo/bar"*
    pub system_path_name: PathBuf,
    pub mountpoint: Mountpoint,
    pub id: u64,
    uuid: Uuid,
    parent_id: Option<u64>,
    parent_uuid: Option<Uuid>,

    time_created: SystemTime,
    time_last_modified: SystemTime,
}




impl Subvolume {

    /// Returns [`Subvolume`] instance whose field name and value corresponds *uniquely* to the set of 
    /// all subvolumes in the system (parsed via [`SubvolumeIter`]). If no such subvolume is found, 
    /// then returns [`None`] instead.
    /// 
    /// If there is more than one [`Subvolume`] which corresponds to the field name and value, then an
    /// error is thrown.
    fn from_field_value<T>(field_name: &str, field_value: T) -> ButterResult<Option<Self>>
    where
        T: 'static + Sized + PartialEq<T>
    {
        let subvolume_iter = SubvolumeIter::from_path(None)?;
        // accumulates all subvolumes which satisfy field name and value
        let mut subvolume_accumulator: Vec<Self> = Vec::new();

        for subvolume_result in subvolume_iter {
            // break from loop if error occurs
            if let Err(error) = subvolume_result {
                return Err(error)
            }
            // can now safely unwrap to subvolume
            let subvolume = subvolume_result.unwrap();

            // check if subvolume has value we desire
            // first get said value
            // panic if  `field_name` not found b/c this should not occur in production
            let Some(value_of_concern) = FieldsIter::new(&subvolume)
                .find(|(name, _)| name == &field_name) 
                .expect(format!("{field_name} not found in struct Subvolume").as_str() )
                .1  // value in (name, value)
                .downcast_ref::<T>() // downcast from Any
            else { continue; };
            
            if value_of_concern != &field_value { continue; }

            subvolume_accumulator.push(subvolume)
        }

        match subvolume_accumulator.len() {
            0 => Ok(None),
            1 => Ok(Some(subvolume_accumulator[0].clone())),
            _ => Err(ButterError::Other(
                "Multiple subvolumes found with".to_string() + field_name
            ))
        }

    }

    /// Retrieves [`Subvolume`] from [path](Path) associated with [`Mountpoint`]
    pub fn from_mountpoint<P: AsRef<Path>>(mountpoint: P) -> ButterResult<Self> {
        
        let mountpoint: Mountpoint = mountpoint.into();

        Self::from_field_value::<Mountpoint>("mountpoint", mountpoint.clone())?
            .ok_or_else(|| ButterError::InvalidMountpoint( (*mountpoint).clone() ) )
    }

    /// Retrieves [`Subvolume`] instance based on BTRFS subvolume id (not to be confused
    /// with [`UUID`](Uuid))
    pub fn from_subvolume_id(id: u64) -> ButterResult<Self> {

        Self::from_field_value::<u64>("id", id.clone())?
            .ok_or_else(|| ButterError::Other(
                format!("Invalid subvolume ID of {id}")
            ))
    }

    /// Retrieves [`Subvolume`] instance from [`UUID`](Uuid)
    pub fn from_uuid(uuid: Uuid) -> ButterResult<Self> {
        
        Self::from_field_value::<Uuid>("uuid", uuid)?
            .ok_or_else(|| ButterError::InvalidUuid(uuid) )
    }


}


impl PartialEq for Subvolume {

    /// Returns `true` if and only if `self.uuid` is equal to `other.uuid`
    fn eq(&self, other: &Self) -> bool {
        self.uuid == other.uuid
    }

    fn ne(&self, other: &Self) -> bool {
        self.uuid != other.uuid
    }

}


impl PartialOrdPathAndTime for Subvolume {

    fn time_created(&self) -> SystemTime {
        self.time_created
    }

    fn time_last_modified(&self) -> SystemTime {
        self.time_last_modified
    }

    fn associated_path(&self) -> &Path {
        self.mountpoint.as_path()
    }

}

impl PartialOrdPathAndTime<Snapshot> for Subvolume {

    fn time_created(&self) -> SystemTime {
        self.time_created
    }

    fn time_last_modified(&self) -> SystemTime {
        self.time_last_modified
    }

    fn associated_path(&self) -> &Path {
        self.mountpoint.as_path()
    }

}

#[derive(Debug)]
pub struct SubvolumeIter;

impl SubvolumeIter {

    /// Returns [`SubvInfoIter`] (also known as [`libbtrfsutil::SubvolumeInfoIterator`]) given some path.
    /// If no path is supplied, defaults to [root path](ROOT).
    fn get_subv_info_iter_from_path(path: Option<PathBuf>) -> ButterResult<SubvInfoIter> {
        let starting_directory = path.unwrap_or(PathBuf::from(ROOT));

        SubvInfoIter::new(
            starting_directory,
            // Subvolume ID for root subvolume
            core::num::NonZeroU64::new( btrfs::FS_TREE_OBJECTID ),
            SubvIterFlags::all(),
        ).map_err(|err| err.into() ) // libbtrfsutil::Error -> ButterError::BtrfsError
    }

    /// Creates an iterator of [subvolumes](Subvolume) relative to `starting_directory`.
    /// If `starting_directory` is `None`, then `starting_directory` defaults
    /// to [root directory](ROOT), or *"/"*.
    pub fn from_path(starting_directory: Option<PathBuf>)
        -> ButterResult<impl Iterator<Item = ButterResult<Subvolume>>> 
    {
        let subv_info_iter = Self::get_subv_info_iter_from_path(starting_directory)?;

        // create generator like that in python
        // translates from SubvInfoIter to custom Iterator
        let iterator = gen!({
            for subvolume_info_result in subv_info_iter {
                // need to propogate and yield errors manually in generator
                // hence somewhat verbose if-let Err(error) guard clauses
                //
                // NOTE: subvolume_info_result is type Result<(PathBuf, SubvInfo), libbtrfsutil::Error>
                if let Err(error) = subvolume_info_result {
                    yield_!( Err( ButterError::BtrfsError(error).into() ) );
                    continue
                }
                // subvolume_info_result now must be Ok((PathBuf, SubvInfo))
                // i.e. safe to unwrap
                let (system_path_name, subvolume_info): (PathBuf, SubvInfo) = 
                        subvolume_info_result.unwrap();
                // now same error handling for mountpoint
                let mountpoint_result: ButterResult<Mountpoint> =
                        Mountpoint::from_uuid(subvolume_info.uuid());
                
                if let Err(error_for_mountpoint) = mountpoint_result {
                    // error_for_mountpoint is type ButterError
                    yield_!( Err(error_for_mountpoint).into() );
                    continue
                }
                // mountpoint can now be unwrapped safely
                let mountpoint: Mountpoint = mountpoint_result.unwrap();
                // translate from Option<NonZeroU64> to Option<u64>
                let subvolume_parent_id: Option<u64> = match subvolume_info.parent_id() {
                    // Convert NonZeroU64 to u64 if Some
                    Some(number_as_non_zero_u64) => Some(number_as_non_zero_u64.get()),
                    None => None,
                };
                // finally, construct Subvolume instance
                let subvolume = Subvolume {
                    system_path_name:   system_path_name,
                    mountpoint:         mountpoint,
                    id:                 subvolume_info.id(),
                    uuid:               subvolume_info.uuid(),
                    parent_id:          subvolume_parent_id,
                    parent_uuid:        subvolume_info.parent_uuid(),
                    time_created:       subvolume_info.created(),
                    time_last_modified: subvolume_info.changed(),
                };
                yield_!(Ok(subvolume));
            }
        }).into_iter(); // convert to Iterator

        Ok(iterator)
    }


}


// ====================================================================================
// ------------------------------------- SNAPSHOTS ------------------------------------
// ====================================================================================


/// Refers to a snapshot of a [`Subvolume`], including relevant metadata which may aid
/// in the data recovery process.
#[derive(Debug, Clone, Builder)]
pub struct Snapshot {
    /// Directory the snapshot is backing up
    pub associated_backup_directory: PathBuf,
    /// The physical subvolume associated with the snapshot
    pub subvolume: Subvolume,
    /// Directory the snapshot is currently placed in
    pub current_mount_location: PathBuf,
    /// [`Tags`](Tag) passed in either manually from the user or automatically from the 
    /// daemon, acting as metadata to tell the program what kind of snapshot this is.
    pub tags: Option<Vec<Tag>>,
    /// Comments passed in by the user through the CLI.
    pub comments: Option<Vec<Comment>>,
}

impl Snapshot {

    pub fn create_subvolume_snapshot(subvolume_to_snapshot: Subvolume) -> ButterResult<()> {
        todo!()
    }

    pub fn create_subvolume_snapshot_from_path<P>(subvolume_mountpoint: P) -> ButterResult<()> 
    where
        P: AsRef<Path>
    {
        todo!()
    }

    /// Gets [`Snapshot`] from its current mount location
    pub fn from_path<P: AsRef<Path>>(path: P) -> ButterResult<Self> {
        todo!()
    }

    
}


impl PartialOrdPathAndTime for Snapshot {

    fn time_created(&self) -> SystemTime {
        self.subvolume.time_created
    }

    fn time_last_modified(&self) -> SystemTime {
        self.subvolume.time_last_modified
    }

    fn associated_path(&self) -> &Path {
        &self.associated_backup_directory
    }

}

impl PartialOrdPathAndTime<Subvolume> for Snapshot {

    fn time_created(&self) -> SystemTime {
        self.subvolume.time_created
    }

    fn time_last_modified(&self) -> SystemTime {
        self.subvolume.time_last_modified
    }

    fn associated_path(&self) -> &Path {
        &self.associated_backup_directory
    }

}

// ====================================================================================
// --------------------------------------- TAGS ---------------------------------------
// ====================================================================================

#[derive(Debug, Clone, EnumString, Display)]
#[strum(ascii_case_insensitive)]
pub enum Tag {
    #[strum(serialize = "O", serialize = "Other"  , to_string = "O")]
    Other,
    #[strum(serialize = "B", serialize = "Boot"   , to_string = "B")]
    Boot,
    #[strum(serialize = "U", serialize = "Update" , to_string = "U")]
    Update,
    #[strum(serialize = "H", serialize = "Hourly" , to_string = "H")]
    Hourly,
    #[strum(serialize = "D", serialize = "Daily"  , to_string = "D")]
    Daily,
    #[strum(serialize = "W", serialize = "Weekly" , to_string = "W")]
    Weekly,
    #[strum(serialize = "M", serialize = "Monthly", to_string = "M")]
    Monthly,
}

// ====================================================================================
// ------------------------------------- COMMMENTS ------------------------------------
// ====================================================================================

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Comment {
    text: String
}

