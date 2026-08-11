// Shared, pure primitives used by model.js (T1 and T2). No closure over
// model parameters.

// Mathematical modulo (always non-negative for positive n), unlike JS `%`
// which is remainder and can be negative. Rocq `mod` corresponds to this.
export function mod(a, n) {
  return ((a % n) + n) % n;
}

// Deep-copy a boolean[][] grid: fresh outer array, fresh rows.
export function copyGrid(g) {
  return g.map(r => r.slice());
}

export function emptyRow(w) {
  return Array(w).fill(false);
}

export function emptyRows(n, w) {
  return Array.from({ length: n }, () => emptyRow(w));
}

// nat subtraction: floors at 0, matching Rocq `nat` subtraction (a - b in ℕ).
export function natSub(a, b) {
  return a > b ? a - b : 0;
}

// nat division: floors, matching Rocq `nat` division (a / b in ℕ).
export function natDiv(a, b) {
  return Math.floor(a / b);
}

// Saturating add: clamps at `max`, testing headroom before forming a+b so the
// sum itself is never computed past `max` (a post-hoc Math.min(max, a+b) is
// unsound once a+b exceeds 2^53). Requires 0 <= a <= max, 0 <= b.
export function capAdd(a, b, max) {
  return b > max - a ? max : a + b;
}
