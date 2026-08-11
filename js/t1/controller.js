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
  rotGrid: eng.rotGrid,
};

const DAS_DELAY = 170;      // ms held before auto-repeat begins
const ARR = 50;              // ms between repeats once shifting
const GRAVITY_PERIOD = 1000; // ms between automatic falls

const KEYMAP = {
  ArrowLeft: 'LEFT', ArrowRight: 'RIGHT', ArrowDown: 'DOWN',
  z: 'CCW', x: 'CW',
};

const GAMEPAD_MAP = new Map([
  [14, 'LEFT'], [15, 'RIGHT'], [13, 'DOWN'],
  [0, 'CCW'], [1, 'CW'],
]);

function randomPiece() {
  return Piece[Math.floor(Math.random() * Piece.length)];
}

export function main(canvas) {
  let machine;
  let lastGravityAt = 0;
  let rafId = null;
  let disposed = false;
  let keyHeld = new Set();
  let prevHeld = {};
  let repeatTimers = {};

  // effects close over `machine` (reassigned by startGame) — must live inside main().
  const ACTIONS = {
    LEFT:  { repeat: true,  effect: () => machine.movePiece(0, -1) },
    RIGHT: { repeat: true,  effect: () => machine.movePiece(0, 1) },
    DOWN:  { repeat: true,  effect: () => machine.fallStep(randomPiece()) },
    CCW:   { repeat: false, effect: () => machine.rotatePiece(false) },
    CW:    { repeat: false, effect: () => machine.rotatePiece(true) },
  };

  function startGame() {
    machine = new eng.Machine(randomPiece());
    keyHeld = new Set();
    prevHeld = {};
    repeatTimers = {};
    lastGravityAt = performance.now();
  }

  function onTick() {
    machine.fallStep(randomPiece());
    if (machine.gameover) handleGameover();
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
            act.effect();
            repeatTimers[name] = { pressedAt: now, lastFire: now };
          } else if (now - t.pressedAt >= DAS_DELAY && now - t.lastFire >= ARR) {
            act.effect();
            t.lastFire = now;
          }
        } else {
          repeatTimers[name] = null;
        }
      } else {
        if (held[name] && !prevHeld[name]) act.effect();
      }
    }

    if (machine.gameover) handleGameover();
    prevHeld = held;
  }

  function frame(now) {
    processInput(now);
    if (!machine.gameover && now - lastGravityAt >= GRAVITY_PERIOD) {
      lastGravityAt = now;
      onTick();
    }
    render(canvas, constants, eng.snapshot(machine), PieceColor);
    if (disposed) return; // dispose() may have fired while this frame was already in flight
    rafId = window.requestAnimationFrame(frame);
  }

  function sizeCanvas() {
    const margin = 0.95;
    const availW = window.innerWidth * margin;
    const availH = window.innerHeight * margin;
    const cell = Math.max(1, Math.floor(Math.min(availW / constants.WM, availH / constants.HM)));
    canvas.width = constants.WM * cell;
    canvas.height = constants.HM * cell;
  }

  function onKeyDown(e) {
    if (machine.gameover) { startGame(); return; }
    const name = KEYMAP[e.key];
    if (!name) return;
    e.preventDefault();
    keyHeld.add(name);
  }

  function onKeyUp(e) {
    const name = KEYMAP[e.key];
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
