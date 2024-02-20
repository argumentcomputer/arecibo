//! Very minimal utilities for reading/writing general arecibo data in disk.
use camino::{Utf8Path, Utf8PathBuf};
use once_cell::sync::OnceCell;
use serde::{de::DeserializeOwned, Serialize};
use std::{
  collections::HashMap,
  fs::{self, File, OpenOptions},
  io::{BufReader, BufWriter},
};

/// Global flag for writing config.
pub static WRITE: bool = false;

/// Path to the directory where Arecibo data will be stored.
pub static ARECIBO_DATA: &str = ".arecibo_data";

/// Global configuration for Arecibo data storage, including root directory and counters.
/// This configuration is initialized on first use.
pub static mut ARECIBO_CONFIG: OnceCell<DataConfig> = OnceCell::new();

/// Configuration for managing Arecibo data files, including the root directory,
/// witness counter, and cross-term counter for organizing files.
#[derive(Debug, Clone)]
pub struct DataConfig {
  root_dir: Utf8PathBuf,
  section_counters: HashMap<String, usize>,
  write_data: bool,
}

/// Initializes the global configuration for Arecibo data storage, setting up the root directory
/// and initializing counters. We create the root directory if it does not already exist.
pub fn init_config() -> DataConfig {
  let root_dir = Utf8PathBuf::from(ARECIBO_DATA);
  if !root_dir.exists() {
    fs::create_dir_all(&root_dir).expect("Failed to create arecibo data directory");
  }

  DataConfig {
    root_dir,
    section_counters: HashMap::new(),
    write_data: WRITE,
  }
}

/// Writes Arecibo data to disk, organizing it into sections and labeling it with a unique identifier.
/// This function serializes the given payload and writes it into the appropriate section and file.
/// For now, we just increment the relevant counter to ensure uniqueness.
pub fn write_arecibo_data<T: Serialize>(
  section: impl AsRef<Utf8Path>,
  label: impl AsRef<Utf8Path>,
  payload: &T,
) {
  let _ = unsafe { ARECIBO_CONFIG.set(init_config()) };
  let config = unsafe { ARECIBO_CONFIG.get_mut().unwrap() };

  let section_path = config.root_dir.join(section.as_ref());
  if !section_path.exists() {
    fs::create_dir_all(&section_path).expect("Failed to create section directory");
  }

  let section = section.as_ref().to_string();
  let counter = config.section_counters.entry(section).or_insert(0);

  let file_path = section_path.join(format!("{}_{:?}", label.as_ref().as_str(), counter));
  *counter += 1;

  let file = OpenOptions::new()
    .read(true)
    .write(true)
    .truncate(true)
    .create(true)
    .open(file_path)
    .expect("Failed to create data file");

  let writer = BufWriter::new(&file);
  bincode::serialize_into(writer, payload).expect("Failed to write data");
}

/// Reads and deserializes data from a specified section and label.
pub fn read_arecibo_data<T: DeserializeOwned>(
  section: impl AsRef<Utf8Path>,
  label: impl AsRef<Utf8Path>,
) -> T {
  let config = unsafe { ARECIBO_CONFIG.get_or_init(init_config) };

  let section_path = config.root_dir.join(section.as_ref());
  assert!(section_path.exists(), "Section directory does not exist");

  // Assuming the label uniquely identifies the file, and ignoring the counter for simplicity
  let file_path = section_path.join(label.as_ref());
  assert!(file_path.exists(), "Data file does not exist");

  let file = File::open(file_path).expect("Failed to open data file");
  let reader = BufReader::new(file);

  bincode::deserialize_from(reader).expect("Failed to read data")
}

/// Are we configured to write data?
pub fn write_data() -> bool {
  let config = unsafe { ARECIBO_CONFIG.get_or_init(init_config) };
  config.write_data
}

/// Set the configuration for writing data.
pub fn set_write_data(write_data: bool) {
  let _ = unsafe { ARECIBO_CONFIG.set(init_config()) };
  let config = unsafe { ARECIBO_CONFIG.get_mut().unwrap() };
  config.write_data = write_data;
}
