// highscores.js — local persistent hall of fame (SP-only). Plain localStorage:
// the data volume here (a handful of entries) doesn't warrant IndexedDB, and
// synchronous access keeps the gameover flow simple (no async plumbing for
// something this small).

import { sanitizeName } from '../t7/protocol.js';

const KEY = 'tetris-tfinal-hof-v1'; // versioned — a later schema change
// shouldn't have to migrate or crash on old data
export const MAX_ENTRIES = 10;

// A stored table is not trusted to be what save() wrote (it can be edited
// by hand, or by another version): entries that are not records with finite
// numeric score/level/lines are dropped, names are cleaned like typed ones
// (sanitizeName), and the result is sorted by score, highest first (stable,
// so equal scores keep their order), and truncated to MAX_ENTRIES.
export function normalize(parsed) {
  if (!Array.isArray(parsed)) return [];
  return parsed
    .filter(
      (e) =>
        e &&
        typeof e === 'object' &&
        [e.score, e.level, e.lines].every(Number.isFinite),
    )
    .map((e) => ({
      name: sanitizeName(e.name) || 'Player',
      score: e.score,
      level: e.level,
      lines: e.lines,
      date: Number.isFinite(e.date) ? e.date : 0,
    }))
    .sort((a, b) => b.score - a.score)
    .slice(0, MAX_ENTRIES);
}

// Inserts `entry` after every entry scoring at least as much (an earlier
// equal score keeps its rank), truncated to MAX_ENTRIES. `row` is the new
// entry's own index, or -1 if it did not make the table.
export function insertEntry(entries, entry) {
  let row = entries.findIndex((e) => e.score < entry.score);
  if (row === -1) row = entries.length;
  const next = [...entries.slice(0, row), entry, ...entries.slice(row)];
  next.length = Math.min(next.length, MAX_ENTRIES);
  return { entries: next, row: row < MAX_ENTRIES ? row : -1 };
}

function load() {
  try {
    const raw = localStorage.getItem(KEY);
    return normalize(raw ? JSON.parse(raw) : []);
  } catch {
    return []; // corrupted data / storage unavailable — fail soft, never crash the game
  }
}

function save(entries) {
  try {
    localStorage.setItem(KEY, JSON.stringify(entries));
  } catch {
    // full, disabled, or private-browsing — silently no-op
  }
}

// Detects whether storage actually works in this browser/session — distinct
// from "empty": some privacy configurations (e.g. Firefox's Enhanced Tracking
// Protection set to block all cookies/storage, not just third-party) make
// every localStorage call silently no-op or throw, for every site, first-party
// included. That's the browser doing exactly what it was configured to do —
// there's no code-side fix for it — but the player should be told why scores
// aren't sticking rather than watching it silently fail.
export function isStorageAvailable() {
  try {
    const probeKey = '__tetris_tfinal_storage_probe__';
    localStorage.setItem(probeKey, '1');
    const ok = localStorage.getItem(probeKey) === '1';
    localStorage.removeItem(probeKey);
    return ok;
  } catch {
    return false;
  }
}

export function getHighScores() {
  return load();
}

// A score qualifies if the table isn't full yet, or it beats the current
// lowest entry — checked before bothering the player with a name prompt.
export function qualifies(score) {
  const entries = load();
  return (
    entries.length < MAX_ENTRIES || score > entries[entries.length - 1].score
  );
}

// Records a score; returns { entries, row }, `row` being the new entry's
// own index (or -1), which the hall of fame highlights — by row, so tied
// scores are not all highlighted. `date` defaults to now.
export function recordScore(name, score, level, lines, date = Date.now()) {
  const result = insertEntry(load(), {
    name: sanitizeName(name) || 'Player',
    score,
    level,
    lines,
    date,
  });
  save(result.entries);
  return result;
}
