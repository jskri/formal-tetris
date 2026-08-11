// highscores.js — local persistent hall of fame (SP-only). Plain localStorage:
// the data volume here (a handful of entries) doesn't warrant IndexedDB, and
// synchronous access keeps the gameover flow simple (no async plumbing for
// something this small).

const KEY = 'tetris-final-hof-v1'; // versioned — a later schema change
                                    // shouldn't have to migrate or crash on old data
const MAX_ENTRIES = 10;

function load() {
  try {
    const raw = localStorage.getItem(KEY);
    const parsed = raw ? JSON.parse(raw) : [];
    return Array.isArray(parsed) ? parsed : [];
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
    const probeKey = '__tetris_final_storage_probe__';
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
  return entries.length < MAX_ENTRIES || score > entries[entries.length - 1].score;
}

export function recordScore(name, score, level, lines) {
  const entries = load();
  entries.push({ name, score, level, lines, date: Date.now() });
  entries.sort((a, b) => b.score - a.score);
  entries.length = Math.min(entries.length, MAX_ENTRIES);
  save(entries);
  return entries;
}
