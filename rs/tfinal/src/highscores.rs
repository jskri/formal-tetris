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

/// Longest name an entry keeps — what name entry lets the player type, and
/// what a loaded file's names are clamped to.
pub const NAME_MAX_LEN: usize = 20;

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
    normalize(serde_json::from_str(&raw).unwrap_or_default())
}

/// The file is outside this program's control (hand-edited, or written by
/// another build), so what `qualifies`/`record_score` and the table rely on
/// is re-established here: sorted descending by score (stable, so ties keep
/// their file order), at most `MAX_ENTRIES`, names without control
/// characters and at most `NAME_MAX_LEN` long.
fn normalize(mut entries: Vec<Entry>) -> Vec<Entry> {
    entries.sort_by_key(|e| std::cmp::Reverse(e.score));
    entries.truncate(MAX_ENTRIES);
    for e in &mut entries {
        e.name = e
            .name
            .chars()
            .filter(|c| !c.is_control())
            .take(NAME_MAX_LEN)
            .collect();
    }
    entries
}

/// Fail-soft: an unwritable filesystem is a silent no-op, never a panic or
/// a surfaced error. Written to a temporary file then renamed over the real
/// one, so an interrupted write leaves the previous table intact instead of
/// a truncated file that would load as empty and then be overwritten.
fn save(entries: &[Entry]) {
    let Some(path) = file_path() else { return };
    let Some(dir) = path.parent() else { return };
    if fs::create_dir_all(dir).is_err() {
        return;
    }
    let Ok(json) = serde_json::to_string_pretty(entries) else {
        return;
    };
    let tmp = path.with_extension("json.tmp");
    if fs::write(&tmp, json).is_ok() && fs::rename(&tmp, &path).is_err() {
        let _ = fs::remove_file(&tmp);
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

/// Loads, inserts, truncates to `MAX_ENTRIES`, persists. Returns the new
/// table and the new entry's index in it (`None` if it didn't make the
/// cut), so the caller can highlight exactly that row even when other
/// entries share its score.
pub fn record_score(
    name: String,
    score: u64,
    level: u64,
    lines: u64,
    date: SystemTime,
) -> (Vec<Entry>, Option<usize>) {
    let mut entries = load();
    let index = insert(
        &mut entries,
        Entry {
            name,
            score,
            level,
            lines,
            date,
        },
    );
    save(&entries);
    (entries, index)
}

/// Inserts `entry` into the sorted table `entries`, after every entry with
/// an equal or higher score (an earlier score of the same value keeps its
/// rank), then truncates to `MAX_ENTRIES`. Returns where it landed.
fn insert(entries: &mut Vec<Entry>, entry: Entry) -> Option<usize> {
    let index = entries
        .iter()
        .take_while(|e| e.score >= entry.score)
        .count();
    entries.insert(index, entry);
    entries.truncate(MAX_ENTRIES);
    (index < MAX_ENTRIES).then_some(index)
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
    fn insert_reports_the_new_entrys_own_row_among_ties() {
        let mut entries = vec![entry(300), entry(200), entry(200), entry(100)];
        assert_eq!(
            insert(&mut entries, entry(200)),
            Some(3),
            "after equal scores"
        );
        let scores: Vec<u64> = entries.iter().map(|e| e.score).collect();
        assert_eq!(scores, vec![300, 200, 200, 200, 100]);

        let mut full: Vec<Entry> = (0..MAX_ENTRIES as u64).rev().map(entry).collect();
        assert_eq!(insert(&mut full, entry(0)), None, "did not make the cut");
        assert_eq!(full.len(), MAX_ENTRIES);
    }

    #[test]
    fn normalize_sorts_truncates_and_cleans_names() {
        let mut raw: Vec<Entry> = (0..(MAX_ENTRIES as u64 + 5)).map(entry).collect();
        raw[12].name = format!("a\nb{}", "x".repeat(100));
        let entries = normalize(raw);
        assert_eq!(entries.len(), MAX_ENTRIES);
        assert!(entries.windows(2).all(|w| w[0].score >= w[1].score));
        assert_eq!(entries[0].score, MAX_ENTRIES as u64 + 4);
        let cleaned = entries.iter().find(|e| e.score == 12).unwrap();
        assert!(cleaned.name.starts_with("abx"));
        assert_eq!(cleaned.name.chars().count(), NAME_MAX_LEN);
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
