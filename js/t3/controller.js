import { T } from './model.js';
import { render } from './view.js';
import {
  Piece, InitialMainGrid, ForbiddenGrid,
  RotGrid, InitialY, InitialX,
  PW, FY, FX, PieceColor,
} from './instance.js';

const eng = T(Piece, InitialMainGrid, ForbiddenGrid,
              RotGrid, InitialY, InitialX, PW, FY, FX);

const constants = {
  HM: InitialMainGrid.length,
  WM: InitialMainGrid[0].length,
  PW, FY, FX,
  FH: ForbiddenGrid.length,
  FW: ForbiddenGrid[0].length,
  rotGrid: eng.T2Eng.T1Eng.rotGrid, // one level deeper than T2's controller
  PANEL_PX: 0, // set by sizeCanvas before the first frame
};

const DAS_DELAY = 170;
const ARR = 50;
const BANNER_MS = 1200;

const BASE_PERIOD = 1000;
const MIN_PERIOD = 16;
const EPS = 1e-6;

// time-per-cell (seconds) = (0.8 − (level−1)·0.007)^(level−1); ms, rounded, floored.
function fallPeriod(level) {
  const base = Math.max(EPS, 0.8 - (level - 1) * 0.007);
  const secs = Math.pow(base, level - 1);
  return Math.max(MIN_PERIOD, Math.round(BASE_PERIOD * secs));
}

const KEYMAP = new Map([
  ['ArrowLeft', 'LEFT'], ['ArrowRight', 'RIGHT'], ['ArrowDown', 'DOWN'],
  ['z', 'CCW'], ['x', 'CW'], [' ', 'HOLD'],
]);

const GAMEPAD_MAP = new Map([
  [14, 'LEFT'], [15, 'RIGHT'], [13, 'DOWN'],
  [0, 'CCW'], [1, 'CW'], [3, 'HOLD'],
]);

function randomPiece() {
  return Piece[Math.floor(Math.random() * Piece.length)];
}

export function main(canvas) {
  let machine;
  let lastGravityAt = 0;
  let currentGravityPeriod = fallPeriod(1);
  let rafId = null;
  let disposed = false;
  let keyHeld = new Set();
  let prevHeld = {};
  let repeatTimers = {};
  let prevLevel = 1;
  let banner = null;
  let prevTotalClearedLines = 0;

  const ACTIONS = {
    LEFT:  { repeat: true,  effect: (now) => { machine.movePiece(0, -1); afterAction(now); } },
    RIGHT: { repeat: true,  effect: (now) => { machine.movePiece(0, 1); afterAction(now); } },
    DOWN:  { repeat: true,  effect: (now) => { machine.fallStep(randomPiece()); afterAction(now); } },
    CCW:   { repeat: false, effect: (now) => { machine.rotatePiece(false); afterAction(now); } },
    CW:    { repeat: false, effect: (now) => { machine.rotatePiece(true); afterAction(now); } },
    HOLD:  { repeat: false, effect: (now) => { machine.holdPiece(randomPiece()); afterAction(now); } },
  };

  // Retargets gravity's period on a level change, restarting the accumulator
  // fresh at `now` — discards whatever had already accumulated toward the
  // previous period, so a level-up always gives a full fresh period at the
  // new speed, off the same clock frame() already uses for input, not a
  // second independent timer.
  function afterAction(now) {
    if (machine.level !== prevLevel) {
      currentGravityPeriod = fallPeriod(machine.level);
      prevLevel = machine.level;
      lastGravityAt = now;
    }

    if (machine.totalClearedLines > prevTotalClearedLines) {
      banner = { combo: machine.combo, perfectClear: machine.perfectClear, t: now };
    }
    prevTotalClearedLines = machine.totalClearedLines;

    if (machine.gameover) handleGameover();
  }

  function onTick(now) {
    machine.fallStep(randomPiece());
    afterAction(now);
  }

  function startGame() {
    machine = new eng.Machine(randomPiece());
    keyHeld = new Set();
    prevHeld = {};
    repeatTimers = {};
    prevLevel = 1;
    banner = null;
    prevTotalClearedLines = 0;
    currentGravityPeriod = fallPeriod(1);
    lastGravityAt = performance.now();
  }

  function handleGameover() {
    keyHeld.clear();
    repeatTimers = {};
  }

  function computeHeld() {
    const held = {};
    for (const name of keyHeld) held[name] = true;
    const gp = navigator.getGamepads?.()?.[0];
    if (gp) {
      for (const [idx, name] of GAMEPAD_MAP)
        if (gp.buttons[idx]?.pressed) held[name] = true;
    }
    return held;
  }

  function processInput(now) {
    const held = computeHeld();

    if (machine.gameover) {
      if (Object.keys(held).some(name => held[name] && !prevHeld[name])) startGame();
      prevHeld = held;
      repeatTimers = {};
      return;
    }

    for (const name of Object.keys(ACTIONS)) {
      const act = ACTIONS[name];
      if (act.repeat) {
        if (held[name]) {
          const t = repeatTimers[name];
          if (!t) {
            act.effect(now);
            repeatTimers[name] = { pressedAt: now, lastFire: now };
          } else if (now - t.pressedAt >= DAS_DELAY && now - t.lastFire >= ARR) {
            act.effect(now);
            t.lastFire = now;
          }
        } else {
          repeatTimers[name] = null;
        }
      } else {
        if (held[name] && !prevHeld[name]) act.effect(now);
      }
    }

    prevHeld = held;
  }

  function frame(now) {
    processInput(now);
    if (!machine.gameover && now - lastGravityAt >= currentGravityPeriod) {
      lastGravityAt = now;
      onTick(now);
    }
    if (banner && now - banner.t > BANNER_MS) banner = null;
    render(canvas, constants, eng.snapshot(machine), PieceColor, banner);
    if (disposed) return; // dispose() may have fired while this frame was already in flight
    rafId = window.requestAnimationFrame(frame);
  }

  function sizeCanvas() {
    const PANEL_FRAC = 0.22, PANEL_MIN = 120, PANEL_MAX = 360;
    const vw = window.innerWidth, vh = window.innerHeight;
    const panel = Math.min(PANEL_MAX, Math.max(PANEL_MIN, Math.round(PANEL_FRAC * vw)));
    const gridMaxW = vw * 0.95 - panel;
    const gridMaxH = vh * 0.95;
    const cell = Math.max(1, Math.floor(Math.min(gridMaxW / constants.WM, gridMaxH / constants.HM)));
    constants.PANEL_PX = panel;
    canvas.width = panel + constants.WM * cell;
    canvas.height = constants.HM * cell;
  }

  function onKeyDown(e) {
    if (machine.gameover) { startGame(); return; }
    const name = KEYMAP.get(e.key);
    if (!name) return;
    e.preventDefault();
    keyHeld.add(name);
  }

  function onKeyUp(e) {
    const name = KEYMAP.get(e.key);
    if (name) keyHeld.delete(name);
  }

  document.addEventListener('keydown', onKeyDown);
  document.addEventListener('keyup', onKeyUp);

  sizeCanvas();
  window.addEventListener('resize', sizeCanvas);
  startGame();
  rafId = window.requestAnimationFrame(frame);

  // Stops the render/gravity loops and removes every listener this call
  // registered — makes main() safe to call again (a fresh main() call after
  // dispose() starts a fully independent game, no leftover state or duplicate
  // handlers from this one).
  return function dispose() {
    disposed = true;
    if (rafId !== null) window.cancelAnimationFrame(rafId);
    rafId = null;
    document.removeEventListener('keydown', onKeyDown);
    document.removeEventListener('keyup', onKeyUp);
    window.removeEventListener('resize', sizeCanvas);
    keyHeld.clear();
    repeatTimers = {};
  };
}
