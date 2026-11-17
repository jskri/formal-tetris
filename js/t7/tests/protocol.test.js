import { describe, test } from 'node:test';
import assert from 'node:assert/strict';
import {
  MAX_PLAYERS,
  NAME_MAX_LEN,
  sanitizeName,
  validState,
  validGarbage,
  validPlayers,
  validFrom,
  decodeWire,
  MAX_WIRE_BYTES,
  MAX_DECODED_BYTES,
} from '../protocol.js';
import { deflateSync } from '../../vendor/fflate.js';

const constants = { HM: 3, WM: 2, PW: 2, Piece: ['A', 'B'] };

function goodState() {
  return {
    type: 'STATE',
    mg: [
      [false, 'A'],
      ['B', false],
      [false, false],
    ],
    p: 'A',
    py: 1,
    px: 0,
    pr: 3,
    gameover: false,
  };
}

describe('validState', () => {
  test('accepts a well-formed STATE', () => {
    assert.strictEqual(validState(goodState(), constants), true);
  });

  test('accepts positions up to one piece width outside the board', () => {
    for (const [py, px] of [
      [-2, -2],
      [4, 3],
    ])
      assert.strictEqual(
        validState({ ...goodState(), py, px }, constants),
        true,
      );
  });

  test('state_with_out_of_range_piece_fields_is_rejected', () => {
    const bad = [
      { p: 'Z' },
      { p: undefined },
      { pr: 4 },
      { pr: -1 },
      { pr: 1.5 },
      { pr: '1' },
      { py: -3 },
      { py: 5 },
      { px: -3 },
      { px: 4 },
      { py: Number.MAX_SAFE_INTEGER },
      { px: NaN },
      { gameover: 'no' },
      { mg: null },
      { mg: [[false, false]] }, // too few rows
      { mg: [[false], [false], [false]] }, // too few columns
      {
        mg: [
          [false, 'garbage'], // not a piece code
          [false, false],
          [false, false],
        ],
      },
    ];
    for (const fields of bad)
      assert.strictEqual(
        validState({ ...goodState(), ...fields }, constants),
        false,
        JSON.stringify(fields),
      );
    assert.strictEqual(validState(null, constants), false);
  });
});

describe('validGarbage', () => {
  const ok = { type: 'GARBAGE', to: 2, amount: 3 };

  test('accepts one other player and an amount in 1..max', () => {
    assert.strictEqual(validGarbage(ok, 1, 3, 14), true);
    assert.strictEqual(validGarbage({ ...ok, amount: 14 }, 1, 3, 14), true);
  });

  test('host_drops_garbage_no_fix_could_have_produced', () => {
    for (const fields of [
      { to: null }, // not addressed to a single player
      { to: 1 }, // to the sender itself
      { to: 3 }, // no such player
      { to: -1 },
      { amount: 0 },
      { amount: 15 },
      { amount: 2.5 },
      { amount: '3' },
    ])
      assert.strictEqual(
        validGarbage({ ...ok, ...fields }, 1, 3, 14),
        false,
        JSON.stringify(fields),
      );
  });
});

describe('validPlayers / validFrom', () => {
  test('accepts a roster and sanitizes its names', () => {
    assert.deepStrictEqual(
      validPlayers({ roster: ['Host', 'a\nb', ''], yourIndex: 2 }),
      ['Host', 'ab', 'P3'],
    );
  });

  test('oversized_start_and_roster_from_the_host_are_bounded', () => {
    const big = Array.from({ length: MAX_PLAYERS + 1 }, (_, i) => `p${i}`);
    assert.strictEqual(validPlayers({ roster: big, yourIndex: 1 }), null);
    const long = validPlayers({
      roster: ['h', 'x'.repeat(1000)],
      yourIndex: 1,
    });
    assert.strictEqual(Array.from(long[1]).length, NAME_MAX_LEN);
  });

  test('rejects malformed rosters and indices', () => {
    for (const msg of [
      { roster: 'Host', yourIndex: 1 },
      { roster: ['Host', 7], yourIndex: 1 },
      { roster: ['Host', 'me'], yourIndex: 0 }, // the host's own index
      { roster: ['Host', 'me'], yourIndex: 2 },
      { roster: ['Host', 'me'], yourIndex: '1' },
    ])
      assert.strictEqual(validPlayers(msg), null, JSON.stringify(msg));
  });

  test('validFrom requires an index of the match', () => {
    assert.strictEqual(validFrom({ from: 0 }, 2), true);
    assert.strictEqual(validFrom({ from: 2 }, 2), false);
    assert.strictEqual(validFrom({}, 2), false);
  });
});

describe('sanitizeName', () => {
  test('pasted_control_characters_are_dropped', () => {
    assert.strictEqual(sanitizeName('Ab\ncd\t\u0007ef'), 'Abcdef');
  });

  test('trims, clamps by code point, and maps non-strings to empty', () => {
    assert.strictEqual(sanitizeName('  bob  '), 'bob');
    const emoji = '😀'.repeat(NAME_MAX_LEN + 5);
    assert.strictEqual(Array.from(sanitizeName(emoji)).length, NAME_MAX_LEN);
    assert.strictEqual(sanitizeName(42), '');
    assert.strictEqual(sanitizeName(undefined), '');
  });
});

describe('decodeWire', () => {
  const encode = (v) =>
    deflateSync(new TextEncoder().encode(JSON.stringify(v)));

  test('round_trips_an_object', () => {
    const msg = { type: 'STATE', from: 1, mg: [[false, 'A']] };
    assert.deepEqual(decodeWire(encode(msg)), msg);
    assert.deepEqual(decodeWire(encode(msg).buffer), msg); // ArrayBuffer, as a data channel delivers
  });

  test('rejects_non_objects', () => {
    assert.equal(decodeWire(encode([1, 2])), null);
    assert.equal(decodeWire(encode('STATE')), null);
    assert.equal(decodeWire(encode(null)), null);
    assert.equal(decodeWire(encode(3)), null);
  });

  test('rejects_corrupt_or_empty_bytes', () => {
    assert.equal(decodeWire(new Uint8Array([1, 2, 3, 4, 5])), null);
    assert.equal(decodeWire(new Uint8Array(0)), null);
    assert.equal(decodeWire('{"type":"STATE"}'), null);
  });

  test('rejects_an_oversized_frame', () => {
    const big = new Uint8Array(MAX_WIRE_BYTES + 1);
    assert.equal(decodeWire(big), null);
  });

  test('rejects_a_frame_inflating_past_the_bound', () => {
    // A small frame that inflates to 1 MiB of a valid-looking JSON string.
    const bomb = encode({ pad: ' '.repeat(1024 * 1024) });
    assert.ok(bomb.byteLength <= MAX_WIRE_BYTES);
    assert.equal(decodeWire(bomb), null);
    // Just under the bound still decodes.
    const ok = encode({ pad: 'x'.repeat(MAX_DECODED_BYTES - 64) });
    assert.equal(decodeWire(ok).pad.length, MAX_DECODED_BYTES - 64);
  });
});
