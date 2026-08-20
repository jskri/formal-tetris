//! spec: T5
//!
//! The T5 engine: `T4.v` plus the piece-drop / shadow mechanics. Wraps
//! `t4::model::Machine<P>` (skill §7) rather than reimplementing any
//! T1–T4 logic; only `gy` and its recomputation are translated here. See
//! `implementation.md` §4–§8.

// ── Params: T5.v adds no new abstract parameter ─────────────────────────────

/// spec: `T5.v` declares no `Parameter` of its own.
pub trait Params: t4::model::Params {}

// ── Invariant checker flag ───────────────────────────────────────────────
pub const CHECK_AXIOMS: bool = true;
pub const CHECK_INVARIANTS: bool = false;

// ── Free functions (T5.v source order, §5) ──────────────────────────────────

/// spec: ShadowYImpl + ShadowY (§4-T5a) — combined into one function, made
/// iterative (skill: a `Fixpoint` on a strictly-decreasing measure becomes
/// a loop). Generic only over `t1::model::Params` (skill §1's minimum-bound
/// rule), taking the innermost `&t1::model::Machine<P>` directly.
///
/// Fuel-bounded, not `py`-bounded — `py` can legitimately go negative, down
/// to `-(PW-1)` (a piece's occupied cells need not sit at local row 0 of its
/// rotation grid), so capping at `py > 0` would stop the search too early.
/// req-piece-shadow.
fn shadow_y<P: t1::model::Params>(s1: &t1::model::Machine<P>) -> i64 {
    let mut py = s1.py;
    let mut fuel = py + P::PW - 1;
    while fuel > 0 {
        if !t1::model::valid::<P, _>(&s1.mg, s1.p, py - 1, s1.px, s1.pr) {
            break;
        }
        py -= 1;
        fuel -= 1;
    }
    py
}

// ── Machine: encapsulates T5.v's State ──────────────────────────────────────

/// spec: State
pub struct Machine<P: Params> {
    pub s4: t4::model::Machine<P>, // spec: s4
    pub gy: i64,                   // spec: gy — req-piece-shadow
}

impl<P: Params> Machine<P> {
    /// spec: Init
    pub fn new(
        bags_fn: impl FnMut(u64) -> Vec<P::Piece>,
        piece_source: impl FnMut() -> P::Piece,
    ) -> Self {
        let s4 = t4::model::Machine::new(bags_fn, piece_source); // spec: T4.Init bags H
        let gy = shadow_y::<P>(&s4.s3.s2.s1); // spec: ShadowY s4
        let m = Machine { s4, gy };
        if CHECK_INVARIANTS {
            check_invariants(&m);
        }
        m
    }

    /// spec: MovePiece — full use (implementation.md §4-T5b): delegate,
    /// then recompute `gy` iff the delegated call fired.
    pub fn move_piece(&mut self, dy: i64, dx: i64) -> bool {
        let fired = self.s4.move_piece(dy, dx);
        if fired {
            self.update_shadow_y();
        }
        if CHECK_INVARIANTS {
            check_invariants(self);
        }
        fired
    }

    /// spec: RotatePiece — full use, same shape as `move_piece`.
    pub fn rotate_piece(&mut self, cw: bool) -> bool {
        let fired = self.s4.rotate_piece(cw);
        if fired {
            self.update_shadow_y();
        }
        if CHECK_INVARIANTS {
            check_invariants(self);
        }
        fired
    }

    /// spec: FixPiece — full use, same shape as `move_piece`.
    pub fn fix_piece(&mut self, bag_new: &[P::Piece]) -> bool {
        let fired = self.s4.fix_piece(bag_new);
        if fired {
            self.update_shadow_y();
        }
        if CHECK_INVARIANTS {
            check_invariants(self);
        }
        fired
    }

    /// spec: HoldPiece — full use, same shape as `move_piece`.
    pub fn hold_piece(&mut self, bag_new: &[P::Piece]) -> bool {
        let fired = self.s4.hold_piece(bag_new);
        if fired {
            self.update_shadow_y();
        }
        if CHECK_INVARIANTS {
            check_invariants(self);
        }
        fired
    }

    /// spec: FallStep. Disjoint-guard sequencing, as T1–T4. No
    /// `check_invariants` call of its own — both branches it can take
    /// already run one.
    pub fn fall_step(&mut self, bag_new: &[P::Piece]) -> bool {
        if self.move_piece(-1, 0) {
            return true; // spec: T5.MovePiece (-1) 0
        }
        self.fix_piece(bag_new) // spec: T5.FixPiece
    }

    /// spec: DropPiece — req-piece-drop (§4-T5d). No-use relocation
    /// (`NewPieceYXState` is a state constructor, not an action) followed by
    /// a full-use `fix_piece`. Single upfront `gameover` guard, no
    /// peek-then-commit — see `proofs.md` §5.
    pub fn drop_piece(&mut self, bag_new: &[P::Piece]) -> bool {
        t4::model::assert_piece_set::<P>(bag_new); // H
        if self.s4.s3.s2.s1.gameover {
            return false; // the only guard this method makes — req-flow
        }
        let px = self.s4.s3.s2.s1.px;
        // spec: NewPieceYXState (gy s, px s) s — req-piece-drop
        t1::model::new_piece_yx_state::<P>(self.gy, px, &mut self.s4.s3.s2.s1);
        self.fix_piece(bag_new) // guaranteed to fire — see proofs.md §5
    }

    /// spec: UpdateShadowY — realized as an in-place mutation (skill §3.2),
    /// `gy` being uniquely owned by `Machine`. `pub` per §6.9: a wrapping
    /// module that mutates `mg` directly needs to recompute the shadow too.
    pub fn update_shadow_y(&mut self) {
        self.gy = shadow_y::<P>(&self.s4.s3.s2.s1);
    }
}

// ── Axiom/invariants checker ────────────────────────────────────────────────

/// spec: `T5.v` states no `Axiom` of its own. Pure delegation.
pub fn check_axioms<P: Params>() {
    t4::model::check_axioms::<P>();
}

/// spec: `LowestShadowY`, `GyEqShadowY` (§6.8) — layered on
/// `t4::model::check_invariants`, gated on `!gameover`: a freshly-spawned
/// piece under `gameover` isn't guaranteed `valid` at its own position.
/// `assert!`, not `debug_assert!` — D7.
pub fn check_invariants<P: Params>(s: &Machine<P>) {
    t4::model::check_invariants(&s.s4);
    if !s.s4.s3.s2.s1.gameover {
        let expected = shadow_y::<P>(&s.s4.s3.s2.s1);
        assert!(s.gy == expected, "GyEqShadowY failed");
        assert!(s.gy <= s.s4.s3.s2.s1.py, "LowestShadowY: gy <= py failed");
    }
}
