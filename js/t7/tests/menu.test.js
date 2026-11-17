import { describe, test } from 'node:test';
import assert from 'node:assert/strict';
import {
  createMenuNav,
  padVendor,
  padLabels,
  PAD_SOUTH,
  PAD_EAST,
  PAD_START,
  PAD_DOWN,
} from '../menu.js';

function pad(pressedButtons, id = 'Generic pad') {
  const buttons = Array.from({ length: 17 }, (_, i) => ({
    pressed: pressedButtons.includes(i),
  }));
  return { id, connected: true, buttons };
}

describe('createMenuNav', () => {
  test('a pad button is one edge, however long it is held', () => {
    const nav = createMenuNav();
    assert.strictEqual(nav.poll(pad([PAD_SOUTH])).padConfirm, true);
    assert.strictEqual(nav.poll(pad([PAD_SOUTH])).padConfirm, false);
    assert.strictEqual(nav.poll(pad([])).padConfirm, false);
    assert.strictEqual(nav.poll(pad([PAD_SOUTH])).padConfirm, true);
  });

  test('a button held through gameplay frames is no fresh confirm afterwards', () => {
    // poll runs every frame, gameplay included: the press is consumed while
    // playing, so the menu screen entered next sees no edge.
    const nav = createMenuNav();
    nav.poll(pad([PAD_SOUTH])); // gameplay frame: CCW pressed
    nav.poll(pad([PAD_SOUTH])); // still held
    assert.strictEqual(nav.poll(pad([PAD_SOUTH])).padConfirm, false); // S9
  });

  test('East is back, Start is pause, D-pad down is down', () => {
    const nav = createMenuNav();
    const e = nav.poll(pad([PAD_EAST, PAD_START, PAD_DOWN]));
    assert.deepStrictEqual(
      [e.back, e.pause, e.down, e.up, e.padConfirm],
      [true, true, true, false, false],
    );
  });

  test('Escape queues back and pause for the next poll only; Enter is not queued', () => {
    const nav = createMenuNav();
    assert.strictEqual(nav.key({ key: 'Escape' }), true);
    assert.strictEqual(nav.key({ key: 'Enter' }), false);
    const e = nav.poll(null);
    assert.strictEqual(e.back && e.pause, true);
    assert.strictEqual(e.padConfirm, false);
    const e2 = nav.poll(null);
    assert.strictEqual(e2.back || e2.pause, false);
  });

  test('arrow keys queue up/down', () => {
    const nav = createMenuNav();
    nav.key({ key: 'ArrowUp' });
    const e = nav.poll(null);
    assert.strictEqual(e.up, true);
    assert.strictEqual(e.down, false);
  });
});

describe('padLabels', () => {
  test('vendor from Chrome and Firefox ids', () => {
    assert.strictEqual(
      padVendor({
        id: 'Wireless Controller (STANDARD GAMEPAD Vendor: 054c Product: 09cc)',
      }),
      '054c',
    );
    assert.strictEqual(
      padVendor({ id: '45e-28e-Xbox 360 Controller' }),
      '045e',
    );
    assert.strictEqual(padVendor({ id: 'Some pad' }), null);
    assert.strictEqual(padVendor(null), null);
  });

  test('brand names, positional fallback, and no pad', () => {
    assert.deepStrictEqual(padLabels(pad([], '045e-0b13-Xbox')), {
      connected: true,
      south: 'A',
      east: 'B',
      north: 'Y',
      start: 'Start',
    });
    assert.strictEqual(padLabels(pad([], '054c-09cc-DS4')).south, 'Cross');
    assert.strictEqual(padLabels(pad([], '057e-2009-Pro')).east, 'A');
    assert.strictEqual(padLabels(pad([], 'unknown')).east, 'East');
    assert.strictEqual(padLabels(null).connected, false);
  });
});
