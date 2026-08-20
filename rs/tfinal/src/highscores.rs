//! Single-player local persistent hall of fame — a JSON file under the
//! platform's per-app data directory. Fail-soft: a missing directory,
//! permissions failure, or corrupt file degrades to an empty list / silent
//! no-op rather than panicking.

use std::fs;
use std::path::PathBuf;
use std::time::SystemTime;

use directories::ProjectDirs;
use serde::{Deserialize, Serialize};

pub const MAX_ENTRIES: usize = 10;

/// Versioned filename — a later schema change starts fresh under a new
/// name instead of migrating or crashing on old data.
const FILE_NAME: &str = "highscores-v1.json";

#[derive(Clone, Serialize, Deserialize)]
pub struct Entry {
    pub name: String,
    pub score: u64,
    pub level: u64,
    pub lines: u64,
    pub date: SystemTime,
}

fn project_dirs() -> Option<ProjectDirs> {
    ProjectDirs::from("", "", "tetris")
}

fn file_path() -> Option<PathBuf> {
    Some(project_dirs()?.data_dir().join(FILE_NAME))
}

/// Fail-soft: missing directory, permissions failure, or corrupt JSON all
/// fall back to an empty list rather than propagating an error.
fn load() -> Vec<Entry> {
    let Some(path) = file_path() else {
        return Vec::new();
    };
    let Ok(raw) = fs::read_to_string(&path) else {
        return Vec::new();
    };
    serde_json::from_str(&raw).unwrap_or_default()
}

/// Fail-soft: an unwritable filesystem is a silent no-op, never a panic or
/// a surfaced error.
fn save(entries: &[Entry]) {
    let Some(path) = file_path() else { return };
    let Some(dir) = path.parent() else { return };
    if fs::create_dir_all(dir).is_err() {
        return;
    }
    if let Ok(json) = serde_json::to_string_pretty(entries) {
        let _ = fs::write(&path, json);
    }
}

/// A real write-then-read-back probe, not merely "does the directory
/// exist" — the failure modes that matter (read-only filesystem, out of
/// space, a sandboxed/no-write environment) only surface on an actual
/// write attempt.
pub fn is_storage_available() -> bool {
    let Some(path) = file_path() else {
        return false;
    };
    let Some(dir) = path.parent() else {
        return false;
    };
    if fs::create_dir_all(dir).is_err() {
        return false;
    }
    let probe = dir.join(".highscores-probe");
    if fs::write(&probe, b"1").is_err() {
        return false;
    }
    let ok = fs::read(&probe).is_ok_and(|c| c == b"1");
    let _ = fs::remove_file(&probe);
    ok
}

pub fn get_high_scores() -> Vec<Entry> {
    load()
}

/// True if the table isn't full yet, or `score` beats the current lowest
/// (entries are kept sorted descending, so the last is the lowest).
pub fn qualifies(entries: &[Entry], score: u64) -> bool {
    entries.len() < MAX_ENTRIES || entries.last().is_some_and(|low| score > low.score)
}

pub fn record_score(
    name: String,
    score: u64,
    level: u64,
    lines: u64,
    date: SystemTime,
) -> Vec<Entry> {
    let mut entries = load();
    entries.push(Entry {
        name,
        score,
        level,
        lines,
        date,
    });
    entries.sort_by_key(|b| std::cmp::Reverse(b.score));
    entries.truncate(MAX_ENTRIES);
    save(&entries);
    entries
}

#[cfg(test)]
mod tests {
    use super::*;

    fn entry(score: u64) -> Entry {
        Entry {
            name: "P".into(),
            score,
            level: 1,
            lines: 0,
            date: SystemTime::UNIX_EPOCH,
        }
    }

    #[test]
    fn qualifies_when_table_not_full() {
        let entries = vec![entry(100)];
        assert!(qualifies(&entries, 1));
    }

    #[test]
    fn qualifies_only_above_current_lowest_when_full() {
        let entries: Vec<Entry> = (0..MAX_ENTRIES as u64)
            .map(|i| entry((i + 1) * 100))
            .collect();
        let lowest = entries.last().unwrap().score;
        assert!(!qualifies(&entries, lowest));
        assert!(qualifies(&entries, lowest + 1));
    }
}
