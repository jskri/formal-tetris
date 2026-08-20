//! spec: T2
//!
//! The T2 engine: `T1.v` plus score/level/combo/perfectClear/
//! totalClearedLines. Wraps `t1::model::Machine<P>` (skill §7) rather than
//! reimplementing any T1 logic; only the definitions genuinely new to
//! `T2.v` are translated here. See `implementation.md` §5–§7.

use t1::model::{Cell, Machine as T1Machine, Params};

// ── Invariant checker flag ───────────────────────────────────────────────
pub const CHECK_AXIOMS: bool = true;
pub const CHECK_INVARIANTS: bool = false;

// ── Free functions (T2.v source order, §5) ──────────────────────────────

/// spec: LineClearPoints
pub fn line_clear_points(cleared_lines: u64, level: u64) -> u64 {
    match cleared_lines {
        0 => 0,
        1 => 100 * level,
        2 => 300 * level,
        3 => 500 * level,
        _ => 800 * level,
    }
}

/// spec: ComboPoints
pub fn combo_points(level: u64, combo: u64) -> u64 {
    if combo > 0 {
        50 * combo * level
    } else {
        0
    }
}

/// spec: PerfectClearPoints
pub fn perfect_clear_points(perfect_clear: bool, cleared_lines: u64, level: u64) -> u64 {
    if !perfect_clear {
        return 0;
    }
    match cleared_lines {
        0 => 0,
        1 => 800 * level,
        2 => 1200 * level,
        3 => 1800 * level,
        _ => 2000 * level,
    }
}

/// spec: Points
pub fn points(cleared_lines: u64, level: u64, combo: u64, perfect_clear: bool) -> u64 {
    line_clear_points(cleared_lines, level)
        + combo_points(level, combo)
        + perfect_clear_points(perfect_clear, cleared_lines, level)
}

/// spec: EmptyGridb — routed through `Cell::occ` (D1). Generic over `T:
/// Cell` directly, not `Option<P::Piece>`: never reads a `Params` item,
/// only occupancy.
pub fn empty_gridb<T: Cell>(g: &[Vec<T>]) -> bool {
    g.iter().all(|row| row.iter().all(|c| !c.occ()))
}

// ── Machine: encapsulates T2.v's State ───────────────────────────────────

/// spec: State
pub struct Machine<P: Params> {
    pub s1: T1Machine<P>,         // spec: s1
    pub score: u64,               // spec: score — req-score-init
    pub level: u64,               // spec: level — req-level-init
    pub combo: u64,               // spec: combo (stored = visible combo + 1)
    pub perfect_clear: bool,      // spec: perfectClear
    pub total_cleared_lines: u64, // spec: totalClearedLines
}

impl<P: Params> Machine<P> {
    /// spec: Init. `check_axioms::<P>()` is not called here (§7): checked
    /// once by the caller before the first `Machine<P>` is constructed.
    pub fn new(p0: P::Piece, piece_source: impl FnMut() -> P::Piece) -> Self {
        let m = Machine {
            s1: T1Machine::new(p0, piece_source), // spec: T1.Init p
            score: 0,                             // req-score-init
            level: 1,                             // req-level-init
            combo: 0,
            perfect_clear: false,
            total_cleared_lines: 0,
        };
        if CHECK_INVARIANTS {
            check_invariants(&m);
        }
        m
    }

    /// spec: MovePiece — full use (§4-T2d): delegate, T2 fields untouched.
    pub fn move_piece(&mut self, dy: i64, dx: i64) -> bool {
        self.s1.move_piece(dy, dx)
    }

    /// spec: RotatePiece — full use (§4-T2d): delegate, scalars unchanged.
    pub fn rotate_piece(&mut self, cw: bool) -> bool {
        self.s1.rotate_piece(cw)
    }

    /// spec: FixPiece — the only non-trivial T2 logic; ordering per §6.4
    /// (`pts` reads the OLD `self.level` before it's overwritten).
    pub fn fix_piece(&mut self, p_new: P::Piece) -> bool {
        let fired = self.s1.fix_piece(p_new); // spec: T1.FixPiece — mutates self.s1 in place
        if !fired {
            return false; // option_map None ⇒ no T2 update
        }
        let cleared_lines = self.s1.cleared_lines as u64; // spec: s1'.(clearedLines)
        let combo2 = if cleared_lines == 0 {
            0
        } else {
            self.combo.saturating_add(1) // spec: combo'
        };
        let perfect_clear2 = empty_gridb(&self.s1.mg); // spec: EmptyGridb s1'.(mg)
        let pts = points(
            cleared_lines,
            self.level,
            combo2.saturating_sub(1),
            perfect_clear2,
        );
        // spec: Points … (combo'-1) — OLD level
        let total2 = self.total_cleared_lines.saturating_add(cleared_lines); // spec: totalClearedLines'

        self.combo = combo2;
        self.perfect_clear = perfect_clear2;
        self.score = self.score.saturating_add(pts); // OLD level already used above
        self.total_cleared_lines = total2;
        self.level = 1 + total2 / 10; // spec: 1 + totalClearedLines'/10 (NEW total)

        if CHECK_INVARIANTS {
            check_invariants(self);
        }
        true
    }

    /// spec: FallStep. `move_piece`'s failure is exactly `fix_piece`'s
    /// guard, so exactly one of the two calls below fires.
    pub fn fall_step(&mut self, p_new: P::Piece) -> bool {
        if self.move_piece(-1, 0) {
            return true; // spec: T2.MovePiece (-1) 0
        }
        self.fix_piece(p_new) // spec: T2.FixPiece
    }
}

// Same axioms as t1.
pub fn check_axioms<P: Params>() {
    t1::model::check_axioms::<P>();
}

/// spec: `T2.Correct`'s `LevelCorrect` conjunct, layered on top of T1's
/// `Correct` (D7): delegates to `t1::model::check_invariants` for
/// everything `s1`-shaped.
pub fn check_invariants<P: Params>(s: &Machine<P>) {
    t1::model::check_invariants(&s.s1);
    assert!(
        s.level == 1 + s.total_cleared_lines / 10,
        "LevelCorrect: level={} but 1 + total_cleared_lines/10={}",
        s.level,
        1 + s.total_cleared_lines / 10
    );
}
