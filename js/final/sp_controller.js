import { T } from '../t6/model.js';
import { render } from '../t6/view.js';
import { renderClearFlash, drawGameOverPartial } from './view.js';
import { sfx, toggleMuted } from './sound.js';
import { qualifies, recordScore, getHighScores, isStorageAvailable } from './highscores.js';
import {
  Piece, InitialMainGrid, ForbiddenGrid,
  RotGrid, InitialY, InitialX,
  PW, FY, FX, NextLen, PieceColor,
} from '../t6/instance.js';

const eng = T(Piece, InitialMainGrid, ForbiddenGrid,
              RotGrid, InitialY, InitialX, PW, FY, FX, NextLen);

const constants = {
  HM: InitialMainGrid.length,
  WM: InitialMainGrid[0].length,
  PW, FY, FX, NextLen,
  Piece,
  FH: ForbiddenGrid.length,
  FW: ForbiddenGrid[0].length,
  rotGrid: eng.T1Eng.rotGrid,
  PANEL_PX: 0,
};

const DAS_DELAY = 170;
const ARR = 50;
const BANNER_MS = 1200;

const BASE_PERIOD = 1000;
const MIN_PERIOD = 16;
const EPS = 1e-6;

const CLEAR_ANIM_MS = 180;  // freeze-and-fade duration for a 1-3 line clear
const TETRIS_ANIM_MS = 320; // longer, punchier duration for a 4-line clear
const SHAKE_AMPLITUDE = 6;  // px, decays to 0 over the Tetris animation
const RESTART_LOCKOUT_MS = 1000; // no restart prompt/input for this long after gameover —
                                  // a frantic last-second key mash shouldn't instantly restart

function normalCurve(t) { return t; }

// Ramps to white slightly ahead of the animation's end, then adds a decaying
// flicker on top so a Tetris reads as a pulse rather than a single fade.
function tetrisCurve(t) {
  const base = Math.min(1, t * 1.3);
  const flicker = Math.sin(t * Math.PI * 6) * (1 - t) * 0.4;
  return Math.max(0, Math.min(1, base + flicker));
}

function fallPeriod(level) {
  const base = Math.max(EPS, 0.8 - (level - 1) * 0.007);
  const secs = Math.pow(base, level - 1);
  return Math.max(MIN_PERIOD, Math.round(BASE_PERIOD * secs));
}

const KEYMAP = new Map([
  ['ArrowLeft', 'LEFT'], ['ArrowRight', 'RIGHT'], ['ArrowDown', 'DOWN'], ['ArrowUp', 'DROP'],
  ['z', 'CCW'], ['x', 'CW'], [' ', 'HOLD'], ['m', 'MUTE'], ['M', 'MUTE'],
]);

const GAMEPAD_MAP = new Map([
  [14, 'LEFT'], [15, 'RIGHT'], [13, 'DOWN'], [12, 'DROP'],
  [0, 'CCW'], [1, 'CW'], [3, 'HOLD'],
]);

function shuffleBag() {
  const a = Piece.slice();
  for (let i = a.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [a[i], a[j]] = [a[j], a[i]];
  }
  return a;
}

function makeBagsFn() {
  const bags = [];
  return (i) => { while (bags.length <= i) bags.push(shuffleBag()); return bags[i]; };
}

// req-piece-kick: try plain rotation first, only attempt a kick if that fails.
function rotate(machine, cw) {
  if (machine.rotatePiece(cw)) return true;
  return machine.rotateKickPiece(cw);
}

// Injects the two overlays this file needs (name-entry, hall-of-fame list)
// into `root`, styled with the same `.overlay`/`.overlay.hidden` classes
// t7/index.html already defines — created dynamically rather than requiring
// static markup elsewhere, so this file stays launchable on its own.
function buildOverlays(root) {
  const nameOverlay = document.createElement('div');
  nameOverlay.className = 'overlay hidden';
  nameOverlay.innerHTML = `
    <h2>New high score!</h2>
    <input type="text" class="hof-name-input" placeholder="Player" maxlength="20" autocomplete="off">
    <button class="hof-name-submit">Submit</button>
  `;
  root.appendChild(nameOverlay);

  const hofOverlay = document.createElement('div');
  hofOverlay.className = 'overlay hidden';
  hofOverlay.innerHTML = `
    <h2>Hall of Fame</h2>
    <div class="hof-entries joiner-list"></div>
    <button class="hof-play-again">Play Again</button>
  `;
  root.appendChild(hofOverlay);

  return {
    nameOverlay,
    nameInput: nameOverlay.querySelector('.hof-name-input'),
    nameSubmit: nameOverlay.querySelector('.hof-name-submit'),
    hofOverlay,
    hofEntries: hofOverlay.querySelector('.hof-entries'),
    playAgainBtn: hofOverlay.querySelector('.hof-play-again'),
  };
}

export function main(canvas, root) {
  let machine;
  let intervalId = null;
  let keyHeld = new Set();
  let prevHeld = {};
  let repeatTimers = {};
  let prevLevel = 1;
  let banner = null;
  let prevTotalClearedLines = 0;
  let clearAnim = null; // { grid, rows, lines, start, duration } while a line-clear flash is playing
  let gameoverAt = null; // timestamp gameover was first detected; null while playing
  let awaitingName = false; // true only while the name-entry overlay is up — blocks restart
  let pendingScore = null; // { score, level, lines } captured at gameover, used once named

  const { nameOverlay, nameInput, nameSubmit, hofOverlay, hofEntries, playAgainBtn } = buildOverlays(root);

  function hideOverlays() {
    nameOverlay.classList.add('hidden');
    hofOverlay.classList.add('hidden');
    awaitingName = false;
  }

  function showNameEntry(scoreInfo) {
    pendingScore = scoreInfo;
    awaitingName = true;
    nameInput.value = '';
    nameOverlay.classList.remove('hidden');
    nameInput.focus();
  }

  function showHallOfFame(entries, highlightScore) {
    hofEntries.innerHTML = '';
    if (!isStorageAvailable()) {
      const notice = document.createElement('div');
      notice.className = 'small';
      notice.textContent = 'High scores can\u2019t be saved in this browser/session \u2014 storage access is blocked.';
      hofEntries.appendChild(notice);
    }
    if (entries.length === 0) {
      const empty = document.createElement('div');
      empty.className = 'small';
      empty.textContent = 'No scores yet \u2014 go set one!';
      hofEntries.appendChild(empty);
    } else {
      entries.forEach((e, i) => {
        const row = document.createElement('div');
        row.className = 'hof-entry' + (e.score === highlightScore ? ' highlight' : '');
        const nameSpan = document.createElement('span');
        nameSpan.textContent = `${i + 1}. ${e.name}`;
        const scoreSpan = document.createElement('span');
        scoreSpan.textContent = `${e.score} (L${e.level}, ${e.lines} lines)`;
        row.appendChild(nameSpan);
        row.appendChild(scoreSpan);
        hofEntries.appendChild(row);
      });
    }
    hofOverlay.classList.remove('hidden');
  }

  function submitName() {
    const name = nameInput.value.trim() || 'Player';
    const entries = recordScore(name, pendingScore.score, pendingScore.level, pendingScore.lines);
    nameOverlay.classList.add('hidden');
    awaitingName = false;
    showHallOfFame(entries, pendingScore.score);
  }

  nameSubmit.addEventListener('click', submitName);
  nameInput.addEventListener('keydown', (e) => {
    e.stopPropagation(); // typing a name must never reach the game's own keydown handler
    if (e.key === 'Enter') submitName();
  });
  playAgainBtn.addEventListener('click', () => { hideOverlays(); startGame(); });

  // Computes the union/full-row preview for a piece that's about to lock at
  // (py, px) — used for both the soft-drop lock (current py/px) and the hard
  // drop lock (py = machine.gy, the shadow row). Bounded to the piece's own
  // vertical footprint (PW rows), not the whole board — HM is unbounded, so
  // a full-height scan on every lock would cost more the taller the board
  // gets, for no benefit: only rows the piece actually touches can newly
  // become full (NoFullLine already guarantees every other row wasn't).
  function precomputeLock(py, px) {
    const s1 = machine.s1;
    const preClearGrid = eng.T1Eng.union(s1.mg, 0, 0, eng.T1Eng.rotGrid(s1.p, s1.pr), py, px);
    const rows = [];
    const yStart = Math.max(py, 0);
    const yEnd = Math.min(py + constants.PW, constants.HM);
    for (let y = yStart; y < yEnd; y++) if (eng.T1Eng.isFullLineb(preClearGrid, y)) rows.push(y);
    return { preClearGrid, rows };
  }

  // Called right after a fixPiece actually fired (soft or hard drop). Plays
  // the lock sound and arms the clear-flash animation if any lines cleared.
  // Sounds that depend on the *cumulative* effect of the clear (combo, perfect
  // clear, level-up) are handled in afterAction() instead, off totalClearedLines/
  // level diffs — those work identically regardless of how the lock happened,
  // so there's no reason to duplicate that detection here.
  function onLocked(preClearGrid, rows, isHardDrop) {
    sfx[isHardDrop ? 'drop' : 'fix']();
    if (rows.length > 0) {
      clearAnim = {
        grid: preClearGrid,
        rows,
        lines: rows.length,
        start: performance.now(),
        duration: rows.length === 4 ? TETRIS_ANIM_MS : CLEAR_ANIM_MS,
      };
    }
  }

  // Shared by the DOWN key and the gravity tick — deliberately not
  // distinguishing player-input from automatic fall (a plain move plays the
  // same sound either way; hard drop makes repeated soft-drop taps rare
  // enough that this isn't the noise concern it would otherwise be).
  function attemptFall(bagNew) {
    const s1 = machine.s1;
    const prevMg = s1.mg;
    const aboutToLock = !eng.T1Eng.canMovePiece(-1, 0, s1);
    const pre = aboutToLock ? precomputeLock(s1.py, s1.px) : null;

    machine.fallStep(bagNew);

    if (machine.s1.mg !== prevMg) {
      onLocked(pre.preClearGrid, pre.rows, false);
    } else {
      sfx.move();
    }
    afterAction();
  }

  function attemptDrop(bagNew) {
    const pre = precomputeLock(machine.gy, machine.s1.px); // dropPiece relocates to gy first
    const ok = machine.dropPiece(bagNew);
    if (ok) onLocked(pre.preClearGrid, pre.rows, true);
    afterAction();
  }

  const ACTIONS = {
    LEFT:  { repeat: true,  effect: () => { if (machine.movePiece(0, -1)) sfx.move(); afterAction(); } },
    RIGHT: { repeat: true,  effect: () => { if (machine.movePiece(0, 1)) sfx.move(); afterAction(); } },
    DOWN:  { repeat: true,  effect: () => attemptFall(shuffleBag()) },
    CCW:   { repeat: false, effect: () => { if (rotate(machine, false)) sfx.rotate(); afterAction(); } },
    CW:    { repeat: false, effect: () => { if (rotate(machine, true)) sfx.rotate(); afterAction(); } },
    HOLD:  { repeat: false, effect: () => { if (machine.holdPiece(shuffleBag())) sfx.hold(); afterAction(); } },
    DROP:  { repeat: false, effect: () => attemptDrop(shuffleBag()) },
  };

  function rescheduleFall() {
    clearInterval(intervalId);
    intervalId = setInterval(onTick, fallPeriod(machine.level));
    prevLevel = machine.level;
  }

  function afterAction() {
    if (machine.level !== prevLevel) {
      sfx.levelUp();
      rescheduleFall();
    }

    const clearedNow = machine.totalClearedLines - prevTotalClearedLines;
    if (clearedNow > 0) {
      sfx.clear(clearedNow);
      if (machine.perfectClear) sfx.perfectClear();
      if (machine.combo > 1) sfx.combo(machine.combo);
      banner = { combo: machine.combo, perfectClear: machine.perfectClear, t: performance.now() };
    }
    prevTotalClearedLines = machine.totalClearedLines;

    if (machine.gameover) handleGameover();
  }

  function onTick() {
    attemptFall(shuffleBag());
  }

  function startGame() {
    machine = new eng.Machine(makeBagsFn());
    keyHeld = new Set();
    prevHeld = {};
    repeatTimers = {};
    prevLevel = 1;
    banner = null;
    prevTotalClearedLines = 0;
    clearAnim = null;
    gameoverAt = null;
    hideOverlays();
    canvas.style.transform = '';
    rescheduleFall();
  }

  function handleGameover() {
    clearInterval(intervalId);
    intervalId = null;
    keyHeld.clear();
    repeatTimers = {};
    gameoverAt = performance.now();
    sfx.gameover();

    const scoreInfo = { score: machine.score, level: machine.level, lines: machine.totalClearedLines };
    setTimeout(() => {
      if (isStorageAvailable() && qualifies(scoreInfo.score)) showNameEntry(scoreInfo);
      else showHallOfFame(getHighScores(), null);
    }, RESTART_LOCKOUT_MS);
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
      const canRestart = !awaitingName && gameoverAt !== null && now - gameoverAt >= RESTART_LOCKOUT_MS;
      if (canRestart && Object.keys(held).some(name => held[name] && !prevHeld[name])) { hideOverlays(); startGame(); }
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

    prevHeld = held;
  }

  function frame(now) {
    processInput(now);
    if (banner && now - banner.t > BANNER_MS) banner = null;

    if (clearAnim) {
      const t = (now - clearAnim.start) / clearAnim.duration;
      if (t >= 1) {
        clearAnim = null;
        canvas.style.transform = '';
      } else {
        const isTetris = clearAnim.lines === 4;
        const progress = isTetris ? tetrisCurve(t) : normalCurve(t);
        renderClearFlash(canvas, constants, eng.snapshot(machine), clearAnim.grid, clearAnim.rows, progress, PieceColor);
        if (isTetris) {
          const amp = SHAKE_AMPLITUDE * (1 - t);
          const dx = (Math.random() * 2 - 1) * amp;
          const dy = (Math.random() * 2 - 1) * amp;
          canvas.style.transform = `translate(${dx.toFixed(1)}px, ${dy.toFixed(1)}px)`;
        }
        window.requestAnimationFrame(frame);
        return;
      }
    }

    const snap = eng.snapshot(machine);
    if (machine.gameover) {
      const cellSize = Math.min((canvas.width - 2 * constants.PANEL_PX) / constants.WM, canvas.height / constants.HM);
      render(canvas, constants, { ...snap, gameover: false }, PieceColor, banner);
      drawGameOverPartial(canvas, constants, cellSize);
    } else {
      render(canvas, constants, snap, PieceColor, banner);
    }
    window.requestAnimationFrame(frame);
  }

  function sizeCanvas() {
    const PANEL_FRAC = 0.22, PANEL_MIN = 120, PANEL_MAX = 360;
    const vw = window.innerWidth, vh = window.innerHeight;
    const totalPanel = Math.min(PANEL_MAX, Math.max(PANEL_MIN, Math.round(PANEL_FRAC * vw)));
    const panel = totalPanel / 2;
    const gridMaxW = vw * 0.95 - 2 * panel;
    const gridMaxH = vh * 0.95;
    const cell = Math.max(1, Math.floor(Math.min(gridMaxW / constants.WM, gridMaxH / constants.HM)));
    constants.PANEL_PX = panel;
    canvas.width = 2 * panel + constants.WM * cell;
    canvas.height = constants.HM * cell;
  }

  document.addEventListener('keydown', (e) => {
    if (e.key === 'm' || e.key === 'M') { toggleMuted(); return; }
    if (document.activeElement === nameInput) return; // typing a name — never treat as game input
    if (machine.gameover) {
      if (!awaitingName && gameoverAt !== null && performance.now() - gameoverAt >= RESTART_LOCKOUT_MS) {
        hideOverlays();
        startGame();
      }
      return;
    }
    const name = KEYMAP.get(e.key);
    if (!name || name === 'MUTE') return;
    e.preventDefault();
    keyHeld.add(name);
  });

  document.addEventListener('keyup', (e) => {
    const name = KEYMAP.get(e.key);
    if (name && name !== 'MUTE') keyHeld.delete(name);
  });

  sizeCanvas();
  window.addEventListener('resize', sizeCanvas);
  startGame();
  window.requestAnimationFrame(frame);
}
