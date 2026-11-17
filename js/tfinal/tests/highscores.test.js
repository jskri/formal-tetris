import { describe, test } from 'node:test';
import assert from 'node:assert/strict';
import { normalize, insertEntry, MAX_ENTRIES } from '../highscores.js';
import { NAME_MAX_LEN } from '../../t7/protocol.js';

const entry = (name, score) => ({ name, score, level: 1, lines: 0, date: 0 });

describe('insertEntry', () => {
  test("insert_reports_the_new_entry's_own_row_among_ties", () => {
    const table = [entry('a', 300), entry('b', 200), entry('c', 200)];
    const { entries, row } = insertEntry(table, entry('new', 200));
    assert.strictEqual(row, 3); // after every equal score
    assert.deepStrictEqual(
      entries.map((e) => e.name),
      ['a', 'b', 'c', 'new'],
    );
  });

  test('a score that does not make a full table reports -1', () => {
    const full = Array.from({ length: MAX_ENTRIES }, (_, i) =>
      entry(`p${i}`, 1000 - i),
    );
    const { entries, row } = insertEntry(full, entry('low', 1));
    assert.strictEqual(row, -1);
    assert.strictEqual(entries.length, MAX_ENTRIES);
    assert.ok(!entries.some((e) => e.name === 'low'));
    assert.strictEqual(insertEntry(full, entry('top', 5000)).row, 0);
  });
});

describe('normalize', () => {
  test('normalize_sorts_truncates_and_cleans_names', () => {
    const raw = [
      entry('low', 10),
      entry('first\n200', 200),
      { name: 'bad', score: 'x', level: 1, lines: 0 },
      null,
      entry('second 200', 200),
      entry('x'.repeat(500), 50),
      ...Array.from({ length: MAX_ENTRIES }, (_, i) => entry(`f${i}`, 5)),
    ];
    const out = normalize(raw);
    assert.strictEqual(out.length, MAX_ENTRIES);
    assert.deepStrictEqual(
      out.slice(0, 4).map((e) => e.name),
      ['first200', 'second 200', 'x'.repeat(NAME_MAX_LEN), 'low'],
    );
    for (let i = 1; i < out.length; i++)
      assert.ok(out[i - 1].score >= out[i].score);
  });

  test('anything but an array is an empty table', () => {
    assert.deepStrictEqual(normalize({ a: 1 }), []);
    assert.deepStrictEqual(normalize(null), []);
  });
});
