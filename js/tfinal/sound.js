// sound.js — procedural sound effects (Web Audio API), no audio assets, no music.

let ctx = null;
let muted = false;

function getCtx() {
  if (!ctx) ctx = new (window.AudioContext || window.webkitAudioContext)();
  if (ctx.state === 'suspended') ctx.resume(); // browsers require a user gesture first
  return ctx;
}

function tone(ac, { freq, duration, type = 'square', gain = 0.15, slideTo = null, delay = 0 }) {
  const start = ac.currentTime + delay;
  const osc = ac.createOscillator();
  const g = ac.createGain();
  osc.type = type;
  osc.frequency.setValueAtTime(freq, start);
  if (slideTo) osc.frequency.exponentialRampToValueAtTime(slideTo, start + duration);
  g.gain.setValueAtTime(gain, start);
  g.gain.exponentialRampToValueAtTime(0.001, start + duration);
  osc.connect(g).connect(ac.destination);
  osc.start(start);
  osc.stop(start + duration);
}

function beep(spec) {
  if (muted) return;
  tone(getCtx(), spec);
}

// Several tones layered/sequenced in one call — shares one AudioContext lookup.
function chord(specs) {
  if (muted) return;
  const ac = getCtx();
  for (const spec of specs) tone(ac, spec);
}

export const sfx = {
  move:   () => beep({ freq: 220, duration: 0.04, type: 'square',   gain: 0.10 }),
  rotate: () => beep({ freq: 330, duration: 0.05, type: 'square',   gain: 0.10 }),

  // Distinct from fix: a deliberate, decisive action, not a piece that quietly
  // ran out of room. Own tone so it's never confused with rotate.
  hold:   () => beep({ freq: 260, duration: 0.06, type: 'triangle', gain: 0.14, slideTo: 400 }),

  fix:    () => beep({ freq: 140, duration: 0.08, type: 'triangle', gain: 0.18 }),

  // Hard drop: sharp downward "thwack" — fast pitch-drop, harder-edged
  // oscillator, short. Reads as decisive commitment, not a gentle landing.
  drop:   () => beep({ freq: 300, duration: 0.06, type: 'square', gain: 0.22, slideTo: 60 }),

  // Pitch/duration scale with lines cleared, so a Tetris (4 lines) reads as
  // more of an event than a single line.
  clear:  (lines) => beep({
    freq: 500 + lines * 60,
    duration: 0.12 + lines * 0.05,
    type: 'sawtooth',
    gain: 0.18,
    slideTo: 1400 + lines * 100,
  }),

  // Bright ascending three-note chime, layered on top of clear() (not a
  // replacement) — clear() says lines cleared, this says it was the rare
  // good outcome. Distinct timbre (sine) from clear's sawtooth sweep.
  perfectClear: () => chord([
    { freq: 900,  duration: 0.10, type: 'sine', gain: 0.16, delay: 0 },
    { freq: 1200, duration: 0.10, type: 'sine', gain: 0.16, delay: 0.09 },
    { freq: 1600, duration: 0.16, type: 'sine', gain: 0.18, delay: 0.18 },
  ]),

  // Rising blip, pitch scales with combo count — an acknowledgment of
  // chaining, not a celebration on its own.
  combo: (comboCount) => beep({
    freq: 500 + Math.min(comboCount, 10) * 40,
    duration: 0.07,
    type: 'square',
    gain: 0.14,
    slideTo: 900 + Math.min(comboCount, 10) * 40,
  }),

  // Brief rising sweep — recurs every 10 lines, so it should read as a nod,
  // not a fanfare.
  levelUp: () => beep({ freq: 400, duration: 0.14, type: 'triangle', gain: 0.16, slideTo: 700 }),

  gameover: () => beep({ freq: 200, duration: 0.5, type: 'sawtooth', gain: 0.15, slideTo: 40 }),

  // Garbage materializing: short and brutal by construction (not adaptive to
  // level) — a hard downward slam, not a graceful transition. Paired with a
  // short, hard screen shake in the controller, not a fade.
  garbageSlam: (rowCount) => beep({
    freq: 180,
    duration: 0.08 + Math.min(rowCount, 8) * 0.01,
    type: 'sawtooth',
    gain: 0.24,
    slideTo: 40,
  }),

  // Winner fanfare: fuller and more triumphant than perfectClear — this is
  // the actual end-of-match payoff, the one time a bigger sound is earned.
  winner: () => chord([
    { freq: 700,  duration: 0.14, type: 'triangle', gain: 0.18, delay: 0 },
    { freq: 900,  duration: 0.14, type: 'triangle', gain: 0.18, delay: 0.12 },
    { freq: 1100, duration: 0.14, type: 'triangle', gain: 0.18, delay: 0.24 },
    { freq: 1400, duration: 0.30, type: 'triangle', gain: 0.20, delay: 0.36 },
  ]),

  // Opponent disconnected: deliberately unobtrusive — informational, not
  // about the local player's own game. Short, low, descending.
  disconnect: () => beep({ freq: 300, duration: 0.12, type: 'sine', gain: 0.10, slideTo: 150 }),

  // Host connection lost: the one alarm-like tone in the set — harsher than
  // anything else, since it means the match is over and needs the player's
  // attention (the "Return to menu" action).
  hostLost: () => chord([
    { freq: 500, duration: 0.15, type: 'square', gain: 0.20, delay: 0 },
    { freq: 500, duration: 0.15, type: 'square', gain: 0.20, delay: 0.2 },
    { freq: 500, duration: 0.15, type: 'square', gain: 0.20, delay: 0.4 },
  ]),
};

export function toggleMuted() { muted = !muted; return muted; }
export function isMuted() { return muted; }
