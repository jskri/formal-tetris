// protocol.js — validation of what crosses the network, and of player names.
//
// Every message a peer sends is untrusted: a modified client can put any JSON
// in a data channel. The checks below are what the controller runs before a
// message reaches a Machine, the renderer, or another peer (§15.3, §15.4). A
// message that fails them is dropped, which corresponds to no T7.v step: the
// message is simply never delivered.

import { inflateSync } from '../vendor/fflate.js';

// Upper bound on a match's roster: caps the host's own slots, and bounds the
// arrays a joiner builds from a host's PLAYERS.
export const MAX_PLAYERS = 16;

// Cap, in Unicode code points, on every player name: typed, pasted, received
// from a peer, or stored in the hall of fame.
export const NAME_MAX_LEN = 64;

// Control characters, and the U+F700–U+F8FF range some platforms use for
// function-key pseudo-characters.
const UNTYPABLE = /[\p{Cc}\u{F700}-\u{F8FF}]/gu;

// A name as shown on screen and sent to peers: untypable characters dropped,
// surrounding whitespace trimmed, clamped to NAME_MAX_LEN code points. A
// non-string yields ''.
export function sanitizeName(s) {
  if (typeof s !== 'string') return '';
  return Array.from(s.replace(UNTYPABLE, '').trim())
    .slice(0, NAME_MAX_LEN)
    .join('');
}

// Bounds on one received frame: its compressed size, and the size it may
// inflate to. Every legitimate message (a STATE's HM×WM grid, a PLAYERS
// roster of MAX_PLAYERS names) is a few KiB at most once inflated; the bounds
// leave a wide margin while keeping a peer from making the receiver allocate
// hundreds of MiB with a small, highly compressible frame.
export const MAX_WIRE_BYTES = 16 * 1024;
export const MAX_DECODED_BYTES = 64 * 1024;

const textDecoder = new TextDecoder();

// Decodes one received frame (deflated JSON bytes) into a plain object, or
// null if it is oversized, inflates past MAX_DECODED_BYTES, is not valid
// deflate/JSON, or is not a plain object. Inflation writes into a fixed
// buffer, which fflate never grows: a result that fills it is treated as
// truncated, hence rejected.
export function decodeWire(data) {
  try {
    const bytes = data instanceof Uint8Array ? data : new Uint8Array(data);
    if (bytes.byteLength === 0 || bytes.byteLength > MAX_WIRE_BYTES)
      return null;
    const out = inflateSync(bytes, {
      out: new Uint8Array(MAX_DECODED_BYTES),
    });
    if (out.length >= MAX_DECODED_BYTES) return null;
    const msg = JSON.parse(textDecoder.decode(out));
    return msg && typeof msg === 'object' && !Array.isArray(msg) ? msg : null;
  } catch {
    return null;
  }
}

function isIndex(i, n) {
  return Number.isInteger(i) && 0 <= i && i < n;
}

// A STATE's fields are drawn straight into an opponent's mini-grid: the piece
// code indexes the rotation table and colours, the rotation must be one of the
// table's four entries, the grid must be exactly HM×WM of `false` or piece
// codes, and the piece position must stay within one piece width of the board
// (any further and no cell of it could be on screen anyway).
// constants: { HM, WM, PW, Piece }.
export function validState(msg, constants) {
  const { HM, WM, PW, Piece } = constants;
  if (!msg || typeof msg !== 'object') return false;
  if (!Piece.includes(msg.p)) return false;
  if (!isIndex(msg.pr, 4)) return false;
  if (!Number.isInteger(msg.py) || msg.py < -PW || msg.py >= HM + PW)
    return false;
  if (!Number.isInteger(msg.px) || msg.px < -PW || msg.px >= WM + PW)
    return false;
  if (typeof msg.gameover !== 'boolean') return false;
  if (!Array.isArray(msg.mg) || msg.mg.length !== HM) return false;
  for (const row of msg.mg) {
    if (!Array.isArray(row) || row.length !== WM) return false;
    for (const c of row) if (c !== false && !Piece.includes(c)) return false;
  }
  return true;
}

// A GARBAGE is addressed to exactly one other player, and carries an amount a
// single fix could have generated: 1..maxAmount, maxAmount being
// generatedGarbage(PW, true) (the most lines one piece can clear, plus a
// perfect clear).
export function validGarbage(msg, fromIdx, playerCount, maxAmount) {
  if (!msg || typeof msg !== 'object') return false;
  if (!isIndex(msg.to, playerCount) || msg.to === fromIdx) return false;
  return (
    Number.isInteger(msg.amount) && 1 <= msg.amount && msg.amount <= maxAmount
  );
}

// A PLAYERS roster: 2..MAX_PLAYERS names, and the receiver's own index, which
// is never the host's (0). Returns the sanitized roster, or null if invalid.
export function validPlayers(msg) {
  if (!msg || typeof msg !== 'object') return null;
  const { roster, yourIndex } = msg;
  if (!Array.isArray(roster) || roster.length > MAX_PLAYERS) return null;
  if (!roster.every((n) => typeof n === 'string')) return null;
  if (!isIndex(yourIndex, roster.length) || yourIndex === 0) return null;
  return roster.map((n, i) => sanitizeName(n) || `P${i + 1}`);
}

// The `from` of a host-relayed GAMEOVER/DISCONNECT names a player of the
// running match.
export function validFrom(msg, playerCount) {
  return !!msg && isIndex(msg.from, playerCount);
}
