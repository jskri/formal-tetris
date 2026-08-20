//! spec: T4
//!
//! The T4 engine: `T3.v` plus the next-pieces preview mechanism (`bag`/
//! `next`). Wraps `t3::model::Machine<P>` (§0.1) rather than reimplementing
//! T1/T2/T3 logic. See `implementation.md` §4–§8.

use std::collections::VecDeque;
use t1::model::Params as T1Params;
use t3::model::Machine as T3Machine;

// ── Params: T4.v's one new abstract parameter ──────────────────────────────

/// spec: NextLen (req-preview-len). `MaxBagLen` is not a trait item — derived
/// everywhere as `P::piece_all().len()` (§3).
pub trait Params: T1Params {
    const NEXT_LEN: i64;
}

// ── Invariant checker flag ───────────────────────────────────────────────
pub const CHECK_AXIOMS: bool = true;
pub const CHECK_INVARIANTS: bool = false;

// ── Free functions (T4.v source order, §5) ────────────────────────────────

/// spec: Bijective/PieceSet (§3) — realized by pigeonhole on the finite
/// representable slice.
pub fn is_piece_set<P: Params>(arr: &[P::Piece]) -> bool {
    let all = P::piece_all();
    arr.len() == all.len()
        && arr.iter().all(|p| all.contains(p))
        && (0..arr.len()).all(|i| (i + 1..arr.len()).all(|j| arr[i] != arr[j]))
}

/// spec: `H` (§3, §8) — a runtime stand-in for the Rocq proof term; checked
/// unconditionally since it validates external input, not a maintained
/// state invariant.
pub fn assert_piece_set<P: Params>(arr: &[P::Piece]) {
    assert!(
        is_piece_set::<P>(arr),
        "PieceSet violated: {arr:?} is not a permutation of Piece"
    );
}

/// spec: DrawNextPiece (§4-T4a) — mutates `bag`/`next` in place, returns
/// `(p, resetting)`; `resetting` read from `bag.len()` before the pop,
/// matching the pre-state reading of `bagLen_ d <=? 1`.
fn draw_once<P: Params>(
    bag: &mut Vec<P::Piece>,
    next: &mut VecDeque<P::Piece>,
    bag_new: &[P::Piece],
) -> (P::Piece, bool) {
    let resetting = bag.len() == 1; // bagLen_ d <=? 1
    let p = next
        .pop_front()
        .expect("next non-empty (BuildInitNext/check_axioms)"); // next_ 0, consumed
    next.push_back(bag.pop().expect("bag non-empty (BagNonEmpty)")); // ShiftNext ... (bag_ (bagLen_-1))
    if resetting {
        bag.clear();
        bag.extend_from_slice(bag_new); // bagSingle branch: refill := bagNew
    }
    (p, resetting)
}

/// spec: BuildInitNext + InitPieceAndDraw (§4-T4b), literal loop translation,
/// generic in `bags_fn`. `bags_fn` must be referentially consistent per
/// index — enforced by the caller (`main.rs`'s memoizing closure), not the
/// type signature.
fn init_piece_and_draw<P: Params>(
    mut bags_fn: impl FnMut(u64) -> Vec<P::Piece>,
) -> (P::Piece, Vec<P::Piece>, VecDeque<P::Piece>) {
    let mut bag = bags_fn(0); // length NUM_PIECES
                              // next's initial contents are arbitrary — every entry is overwritten
                              // within NEXT_LEN draws below; only the length matters up front.
    let filler = bag[0];
    let mut next: VecDeque<P::Piece> = std::iter::repeat(filler)
        .take(P::NEXT_LEN as usize)
        .collect();
    let mut bag_idx: u64 = 1;
    for _ in 0..P::NEXT_LEN {
        let (_, resetting) = draw_once::<P>(&mut bag, &mut next, &bags_fn(bag_idx));
        if resetting {
            bag_idx += 1;
        }
    }
    let (p, _) = draw_once::<P>(&mut bag, &mut next, &bags_fn(bag_idx));
    (p, bag, next)
}

// ── Machine: encapsulates T4.v's State ────────────────────────────────────

/// spec: State
pub struct Machine<P: Params> {
    pub s3: T3Machine<P>,         // spec: s3
    pub bag: Vec<P::Piece>,       // spec: bag_ (Draw.bag_); bagLen_ = bag.len(), not stored
    pub next: VecDeque<P::Piece>, // spec: next_ (Draw.next_); length NEXT_LEN
}

impl<P: Params> Machine<P> {
    /// spec: Init (§6.1). `piece_source` has no `T4.v` counterpart, kept
    /// separate from `bags_fn` since the two draw from unrelated domains.
    /// `check_axioms::<P>()` is not called here — checked once by the caller
    /// before the first `Machine<P>` of any given `P` is constructed, same
    /// convention as `t1`/`t3::model::Machine::new`.
    pub fn new(
        mut bags_fn: impl FnMut(u64) -> Vec<P::Piece>,
        piece_source: impl FnMut() -> P::Piece,
    ) -> Self {
        let checked_bags_fn = |i: u64| {
            let b = bags_fn(i);
            assert_piece_set::<P>(&b); // H, per-index (§4-T4c)
            b
        };
        let (p, bag, next) = init_piece_and_draw::<P>(checked_bags_fn);
        let m = Machine {
            s3: T3Machine::new(p, piece_source), // spec: T3.Init p
            bag,
            next,
        };
        if CHECK_INVARIANTS {
            check_invariants(&m);
        }
        m
    }

    /// spec: MovePiece — full use (§4-T4f): delegate, bag/next untouched.
    pub fn move_piece(&mut self, dy: i64, dx: i64) -> bool {
        self.s3.move_piece(dy, dx)
    }

    /// spec: RotatePiece — full use (§4-T4f): delegate, bag/next untouched.
    pub fn rotate_piece(&mut self, cw: bool) -> bool {
        self.s3.rotate_piece(cw)
    }

    /// spec: FixPiece — partial use (§4-T4d): peek `next.front()` before
    /// the guard, commit only on success, giving "guard fails ⟹ zero
    /// mutation" of `bag`/`next`.
    pub fn fix_piece(&mut self, bag_new: &[P::Piece]) -> bool {
        assert_piece_set::<P>(bag_new); // H
        let p = *self.next.front().expect("next non-empty"); // pure read — no mutation yet
        let fired = self.s3.fix_piece(p); // spec: T3.FixPiece (next s 0)
        if !fired {
            return false; // zero mutation of bag/next — matches every other guard
        }
        self.draw_next_piece(bag_new); // commit, now that fired is confirmed
        if CHECK_INVARIANTS {
            check_invariants(self);
        }
        true
    }

    /// spec: FallStep (§4-T4e) — disjoint-guard sequencing, as in T1–T3.
    pub fn fall_step(&mut self, bag_new: &[P::Piece]) -> bool {
        if self.move_piece(-1, 0) {
            return true; // spec: T4.MovePiece (-1) 0
        }
        self.fix_piece(bag_new) // spec: T4.FixPiece — re-checks bag_new (§4-T4c), accepted redundancy
    }

    /// spec: HoldPiece — partial use (§4-T4g, hazard note §4-T4h): draws
    /// only when `hold` was empty; `self.s3.hold`/`swapped` stay owned
    /// entirely by `self.s3.hold_piece`.
    pub fn hold_piece(&mut self, bag_new: &[P::Piece]) -> bool {
        assert_piece_set::<P>(bag_new); // H
        if self.s3.s2.s1.gameover {
            return false; // T4's own guard (T4.v's `if !gameover`)
        }
        let p2 = match self.s3.hold {
            Some(h) => h,
            None => self.draw_next_piece(bag_new), // only branch that mutates bag/next
        };
        let fired = self.s3.hold_piece(p2);
        if !fired {
            return false; // unreachable given SwappedImplyHoldSome (§4-T4h); kept as a real check
        }
        if CHECK_INVARIANTS {
            check_invariants(self);
        }
        true
    }

    /// spec: DrawNextPiece (§6.10), wrapped against `self`'s own fields.
    /// `resetting` discarded here; only `init_piece_and_draw` needs it.
    fn draw_next_piece(&mut self, bag_new: &[P::Piece]) -> P::Piece {
        draw_once::<P>(&mut self.bag, &mut self.next, bag_new).0
    }
}

// ── Axiom/invariants checker ────────────────────────────────────────────────

/// spec: AxiomsMaxBagLen (§6.8) — `T4.v`'s only stated axiom. Composes
/// `t1::model::check_axioms::<P>()`.
pub fn check_axioms<P: Params>() {
    t1::model::check_axioms::<P>();
    // AxiomsMaxBagLen (§6.8): NUM_PIECES must be > 0.
    assert!(
        !P::piece_all().is_empty(),
        "AxiomsMaxBagLen: NUM_PIECES (= |Piece|) must be > 0"
    );
    // NEXT_LEN > 0 is an implementation requirement, not a T4.v axiom (§6.8).
    assert!(
        P::NEXT_LEN > 0,
        "NEXT_LEN must be > 0 (implementation requirement, not a T4.v axiom)"
    );
}

/// spec: `TypeOK`'s representable analogue, `BagNonEmpty`, `next`
/// well-formedness (§6.9), layered on `t3::model::check_invariants`. Every
/// conjunct is `assert!`, not `debug_assert!` (t1/implementation.md D7).
pub fn check_invariants<P: Params>(s: &Machine<P>) {
    t3::model::check_invariants(&s.s3);
    let num_pieces = P::piece_all().len();
    assert!(!s.bag.is_empty(), "BagNonEmpty failed");
    assert!(s.bag.len() <= num_pieces, "bag length bound failed");
    assert!(
        (0..s.bag.len()).all(|i| (i + 1..s.bag.len()).all(|j| s.bag[i] != s.bag[j])),
        "bag elements not pairwise distinct"
    );
    assert!(
        s.bag.iter().all(|p| P::piece_all().contains(p)),
        "bag ⊆ Piece failed"
    );
    assert!(s.next.len() == P::NEXT_LEN as usize, "next length failed");
    assert!(
        s.next.iter().all(|p| P::piece_all().contains(p)),
        "next ⊆ Piece failed"
    );
}
