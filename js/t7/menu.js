// menu.js — gamepad/keyboard menu navigation, shared by every controller that
// shows menus: the pad reader, per-frame menu edges, pad-brand labels, the
// controls tables, the in-game menu overlay, and the game screens' menu hint.
// Display and input plumbing only; no model call is made from here.

// Standard Gamepad mapping (https://w3c.github.io/gamepad/#remapping):
// buttons are always read by position, whatever the pad's brand.
export const PAD_SOUTH = 0;
export const PAD_EAST = 1;
export const PAD_NORTH = 3;
export const PAD_START = 9;
export const PAD_UP = 12;
export const PAD_DOWN = 13;

const HINT_COLOR = '#888888';
const HINT_MIN_FONT = 10;
const HINT_MAX_FONT = 14;

// The first connected pad, or null. Only the focused window reads it: the
// browser exposes the pad to every window, while the keyboard goes to the
// focused one only, so two game windows on one computer would otherwise both
// act on one pad. A button held while focus comes back then counts as a
// fresh press, once.
export function readPad() {
  if (typeof document !== 'undefined' && !document.hasFocus()) return null;
  return firstPad();
}

// The first connected pad, focused window or not: what the controls tables
// describe.
export function firstPad() {
  const pads = navigator.getGamepads?.() ?? [];
  for (const gp of pads) if (gp && gp.connected) return gp;
  return null;
}

function pressed(gp, i) {
  return !!gp?.buttons[i]?.pressed;
}

// Per-frame menu edges: { up, down, confirm, back, pause }. `poll` must run
// once per frame on every screen, gameplay included, so the pad's previous
// state is always current: a button held through a screen change is then not
// a fresh press on the next screen. Keyboard edges are queued by `key` from
// the controller's keydown handler and consumed by the next `poll`:
// Escape is both back and pause, ↑/↓ move. Enter needs no queuing: it
// activates the focused button natively.
export function createMenuNav() {
  let prev = {};
  let queued = {};
  return {
    key(e) {
      if (e.key === 'Escape') {
        queued.back = true;
        queued.pause = true;
        return true;
      }
      if (e.key === 'ArrowUp' || e.key === 'ArrowDown') {
        queued[e.key === 'ArrowUp' ? 'up' : 'down'] = true;
        return true;
      }
      return false;
    },
    poll(gp) {
      const held = {
        up: pressed(gp, PAD_UP),
        down: pressed(gp, PAD_DOWN),
        confirm: pressed(gp, PAD_SOUTH),
        back: pressed(gp, PAD_EAST),
        pause: pressed(gp, PAD_START),
      };
      const nav = {};
      for (const k of Object.keys(held))
        nav[k] = (held[k] && !prev[k]) || !!queued[k];
      // `confirm` from the pad only: the keyboard's Enter clicks natively.
      nav.padConfirm = held.confirm && !prev.confirm;
      prev = held;
      queued = {};
      return nav;
    },
  };
}

// Moves focus among a container's enabled, visible stops (buttons, text
// fields) on up/down, and clicks the focused button on the pad's confirm.
// Returns true if anything happened.
export function navigateStops(container, nav) {
  const stops = Array.from(
    container.querySelectorAll(
      'button:not([disabled]), input:not([disabled]), textarea:not([disabled])',
    ),
  ).filter((el) => el.offsetParent !== null || el.getClientRects().length > 0);
  if (stops.length === 0) return false;
  const cur = stops.indexOf(document.activeElement);
  if (nav.down) {
    stops[(cur + 1) % stops.length].focus();
    return true;
  }
  if (nav.up) {
    stops[cur <= 0 ? stops.length - 1 : cur - 1].focus();
    return true;
  }
  if (nav.padConfirm) {
    if (cur === -1) stops[0].focus();
    else if (stops[cur].tagName === 'BUTTON') stops[cur].click();
    return true;
  }
  return false;
}

// Button names of the connected pad's brand, from the USB vendor ID in its
// `id` (Chrome: "… (Vendor: 054c Product: 09cc)", Firefox: "054c-09cc-…").
// Any other vendor, or none, gets the positional names. Display only.
const BRAND_LABELS = {
  '045e': { south: 'A', east: 'B', north: 'Y', start: 'Start' }, // Microsoft
  '054c': {
    south: 'Cross',
    east: 'Circle',
    north: 'Triangle',
    start: 'Options',
  }, // Sony
  '057e': { south: 'B', east: 'A', north: 'X', start: '+' }, // Nintendo
};
const POSITIONAL_LABELS = {
  south: 'South',
  east: 'East',
  north: 'North',
  start: 'Start',
};

export function padVendor(gp) {
  if (!gp?.id) return null;
  const m =
    /vendor:\s*([0-9a-f]{1,4})/i.exec(gp.id) ??
    /^([0-9a-f]{1,4})-[0-9a-f]{1,4}-/i.exec(gp.id);
  return m ? m[1].toLowerCase().padStart(4, '0') : null;
}

// { connected, south, east, north, start }; `connected` false with no pad.
export function padLabels(gp) {
  const names = BRAND_LABELS[padVendor(gp)] ?? POSITIONAL_LABELS;
  return { connected: !!gp, ...names };
}

// A button named in running text, where no "Gamepad" header says it is one.
export function buttonName(name) {
  return `${name} button`;
}

// Control rows: [key, pad cell, action]. A pad cell is a label name
// ('south', 'east', 'north', 'start'), a literal (D-pad arrows), or null for
// keyboard-only actions.
const MOVE = ['↑/↓', 'D-pad ↑/↓', 'move'];
const SELECT = ['Enter', 'south', 'select'];
const BACK = ['Esc', 'east', 'back'];
export const CONTROL_SETS = {
  nav: [MOVE, SELECT],
  menu: [MOVE, SELECT, BACK],
  lobby: [
    MOVE,
    SELECT,
    BACK,
    ['Ctrl-C', null, 'copy'],
    ['Ctrl-V', null, 'paste'],
  ],
  game: [
    ['←/→', 'D-pad ←/→', 'move'],
    ['↓', 'D-pad ↓', 'soft drop'],
    ['↑', 'D-pad ↑', 'hard drop'],
    ['X', 'east', 'rotate right'],
    ['Z', 'south', 'rotate left'],
    ['Space', 'north', 'hold'],
    ['Esc', 'start', 'menu'],
  ],
};

// A Key / Gamepad / Action table; the Gamepad column is left out with no pad.
// The header is what tells a pad's "B" apart from the B key, so cells carry
// no "button" suffix.
export function controlsTable(rows, labels) {
  const table = document.createElement('table');
  table.className = 'controls';
  const header = labels.connected
    ? ['Key', 'Gamepad', 'Action']
    : ['Key', 'Action'];
  const body = rows.map(([key, pad, action]) => {
    const padCell = pad === null ? '' : (labels[pad] ?? pad);
    return labels.connected ? [key, padCell, action] : [key, action];
  });
  for (const [i, cells] of [header, ...body].entries()) {
    const tr = document.createElement('tr');
    for (const c of cells) {
      const td = document.createElement(i === 0 ? 'th' : 'td');
      td.textContent = c;
      tr.appendChild(td);
    }
    table.appendChild(tr);
  }
  return table;
}

// Rebuilds every `[data-controls="<set>"]` element under root.
export function refreshControls(root, labels) {
  for (const el of root.querySelectorAll('[data-controls]')) {
    const rows = CONTROL_SETS[el.dataset.controls];
    if (rows) el.replaceChildren(controlsTable(rows, labels));
  }
}

// Calls `onChange(labels)` whenever the connected pad or its brand changes,
// checked once per frame by `update(gp)`. The first call always reports.
export function createLabelWatch(onChange) {
  let key = undefined;
  let labels = padLabels(null);
  return {
    update(gp) {
      const k = gp ? `${padVendor(gp)}` : '';
      if (k !== key) {
        key = k;
        labels = padLabels(gp);
        onChange(labels);
      }
      return labels;
    },
    get labels() {
      return labels;
    },
  };
}

const MENU_STYLE = `
  .game-menu { position: absolute; inset: 0; display: flex; flex-direction: column;
    align-items: center; justify-content: center; gap: 8px; color: #eee;
    background: rgba(0,0,0,0.75); font-family: sans-serif; z-index: 10; }
  .game-menu.hidden { display: none; }
  .game-menu button { padding: 8px 16px; min-width: 140px; cursor: pointer; }
  .game-menu button:focus { outline: 3px solid #fabd2f; }
  .game-menu .controls-title { margin-top: 18px; color: #aaa; font-size: 0.85em; }
  table.controls { border-collapse: collapse; font-family: monospace; font-size: 0.85em;
    color: #aaa; margin-top: 10px; }
  table.controls th, table.controls td { padding: 1px 10px; text-align: left; }
  table.controls th { color: #888; font-weight: normal; }
`;

function ensureStyle() {
  if (document.getElementById('game-menu-style')) return;
  const style = document.createElement('style');
  style.id = 'game-menu-style';
  style.textContent = MENU_STYLE;
  document.head.appendChild(style);
}

// The in-game menu: an overlay with a title, one button per item, then the
// game's controls. `onChoose(index)` runs when an item is activated (click,
// Enter, or the pad's confirm via `step`). The overlay is owned by the screen
// it was opened on: the controller closes it on any screen change.
export function createGameMenu(root) {
  ensureStyle();
  const el = document.createElement('div');
  el.className = 'game-menu hidden';
  const title = document.createElement('h2');
  const items = document.createElement('div');
  items.style.display = 'flex';
  items.style.flexDirection = 'column';
  items.style.gap = '8px';
  const controlsTitle = document.createElement('div');
  controlsTitle.className = 'controls-title';
  controlsTitle.textContent = 'Game controls:';
  const controls = document.createElement('div');
  controls.dataset.controls = 'game';
  el.append(title, items, controlsTitle, controls);
  root.appendChild(el);

  let open = false;

  return {
    get isOpen() {
      return open;
    },
    // Opens with `labels` (string[]); onChoose(index) on activation.
    open(titleText, labels, onChoose) {
      title.textContent = titleText;
      items.replaceChildren(
        ...labels.map((text, i) => {
          const b = document.createElement('button');
          b.textContent = text;
          b.addEventListener('click', () => onChoose(i));
          return b;
        }),
      );
      el.classList.remove('hidden');
      open = true;
      items.querySelector('button')?.focus();
    },
    setTitle(text) {
      title.textContent = text;
    },
    setItemText(i, text) {
      const b = items.querySelectorAll('button')[i];
      if (b) b.textContent = text;
    },
    close() {
      if (!open) return;
      open = false;
      el.classList.add('hidden');
      if (el.contains(document.activeElement)) document.activeElement.blur();
    },
    // One frame of menu input. Returns 'close' when back or pause asks the
    // menu to close (like Continue), otherwise null. The caller never steps
    // the menu on the frame it opened it, so the Escape that opened it does
    // not also close it.
    step(nav) {
      if (!open) return null;
      if (nav.back || nav.pause) return 'close';
      navigateStops(items, nav);
      return null;
    },
    element: el,
  };
}

// "[Esc/<Start> button] menu", in the hint colour on the board's left, aligned
// with the board's bottom; the font shrinks (down to HINT_MIN_FONT) to fit
// the left panel. Running text, so the pad button carries the "button" suffix.
export function drawMenuHint(canvas, constants, labels) {
  const ctx = canvas.getContext('2d');
  const text = labels.connected
    ? `[Esc/${buttonName(labels.start)}] menu`
    : '[Esc] menu';
  const margin = 6;
  const avail = Math.max(1, (constants.PANEL_PX ?? 0) - 2 * margin);
  let size = HINT_MAX_FONT;
  ctx.font = `${size}px sans-serif`;
  const w = ctx.measureText(text).width;
  if (w > avail) size = Math.max(HINT_MIN_FONT, Math.floor((size * avail) / w));
  ctx.save();
  ctx.font = `${size}px sans-serif`;
  ctx.fillStyle = HINT_COLOR;
  ctx.textAlign = 'left';
  ctx.textBaseline = 'bottom';
  ctx.fillText(text, margin, canvas.height - margin);
  ctx.restore();
}
