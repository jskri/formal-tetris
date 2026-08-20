//! spec: T3
//!
//! The T3 engine: `T2.v` plus a hold slot (`hold`/`swapped`). Wraps
//! `t2::model::Machine<P>` (skill §7) rather than reimplementing any T1/T2
//! logic; only `HoldPiece` — the one definition genuinely new to `T3.v` —
//! is translated here. See `implementation.md` §4–§8.

use t1::model::{new_piece_state, Params};
use t2::model::Machine as T2Machine;

// ── Invariant checker flag ───────────────────────────────────────────────
pub const CHECK_AXIOMS: bool = true;
pub const CHECK_INVARIANTS: bool = false;

// ── Free functions (T3.v source order, §5) ────────────────────────────────
// None — `T3.v` defines no new free function; `HoldPiece`'s logic reaches
// `t1::model::new_piece_state` (§4-T3a), not redefined here.

// ── Machine: encapsulates T3.v's State ────────────────────────────────────

/// spec: State
pub struct Machine<P: Params> {
    pub s2: T2Machine<P>,       // spec: s2
    pub hold: Option<P::Piece>, // spec: hold
    pub swapped: bool,          // spec: swapped
}

impl<P: Params> Machine<P> {
    /// spec: Init. `check_axioms::<P>()` is not called here — axioms
    /// constrain parameters, not state, and run once before the first
    /// `Machine<P>` of a given `P` (`implementation.md` §7).
    pub fn new(p0: P::Piece, piece_source: impl FnMut() -> P::Piece) -> Self {
        let m = Machine {
            s2: T2Machine::new(p0, piece_source), // spec: T2.Init p
            hold: None,                           // spec: None
            swapped: false,
        };
        if CHECK_INVARIANTS {
            check_invariants(&m);
        }
        m
    }

    /// spec: MovePiece — full use (skill §7.1): delegate, hold/swapped
    /// untouched.
    pub fn move_piece(&mut self, dy: i64, dx: i64) -> bool {
        self.s2.move_piece(dy, dx)
    }

    /// spec: RotatePiece — full use: delegate, hold/swapped untouched.
    pub fn rotate_piece(&mut self, cw: bool) -> bool {
        self.s2.rotate_piece(cw)
    }

    /// spec: FixPiece — partial use (skill §7.1): delegate, then req-hold-limit.
    pub fn fix_piece(&mut self, p_new: P::Piece) -> bool {
        let fired = self.s2.fix_piece(p_new); // spec: T2.FixPiece — mutates self.s2 in place
        if !fired {
            return false; // option_map None ⇒ no T3 update
        }
        self.swapped = false; // req-hold-limit: holding is allowed again after fixing
        if CHECK_INVARIANTS {
            check_invariants(self);
        }
        true
    }

    /// spec: FallStep — disjoint-guard sequencing (skill §6.4): `move_piece`
    /// failing is exactly `fix_piece`'s guard, so exactly one call fires.
    pub fn fall_step(&mut self, p_new: P::Piece) -> bool {
        if self.move_piece(-1, 0) {
            return true; // spec: T3.MovePiece (-1) 0
        }
        self.fix_piece(p_new) // spec: T3.FixPiece
    }

    /// spec: HoldPiece — no use (skill §7.1): the only genuinely new T3
    /// logic, translated and proved fresh (`implementation.md` §4-T3e, §8.5).
    pub fn hold_piece(&mut self, p_new: P::Piece) -> bool {
        if !(!self.s2.s1.gameover && !self.swapped) {
            return false; // real guard (req-hold-limit)
        }
        let p2 = self.hold.unwrap_or(p_new); // req-hold-swap / req-hold-empty
        let old_p = self.s2.s1.p; // 1: read BEFORE new_piece_state overwrites it
        new_piece_state::<P>(p2, &mut self.s2.s1); // spec: NewPieceState p2 (s1 s2_) — in place
        self.hold = Some(old_p); // 2: req-hold
        self.swapped = true; // 3: req-hold-limit
        if CHECK_INVARIANTS {
            check_invariants(self);
        }
        true
    }
}

// Same axioms as t2.
pub fn check_axioms<P: Params>() {
    t2::model::check_axioms::<P>();
}

/// spec: `T3.Correct`'s two new conjuncts (`SwappedImplyHoldSome`,
/// `GameoverImplyNotSwapped`), on top of T2's `Correct`. `assert!`, not
/// `debug_assert!`, per D7. Delegates to `t2::model::check_invariants` for
/// the `s2`-shaped conjuncts.
pub fn check_invariants<P: Params>(s: &Machine<P>) {
    t2::model::check_invariants(&s.s2);
    assert!(
        !s.swapped || s.hold.is_some(),
        "SwappedImplyHoldSome: swapped=true but hold=None"
    );
    assert!(
        !s.s2.s1.gameover || !s.swapped,
        "GameoverImplyNotSwapped: gameover=true but swapped=true"
    );
    // `hold ∈ Piece ∪ {None}` is type-level (D8) — no runtime assertion needed.
}
