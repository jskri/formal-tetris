//! spec: T7
//!
//! The T7 engine: `T6.v` generalized to the multi-player game, plus the
//! network layer's local half (garbage, target, gameover/connected views).
//! `Machine<P>` wraps `t6::model::Machine<P>` (skill §7) as `self.s6`
//! (`implementation.md` §1). This module implements no T1–T6 game logic —
//! movement, rotation, line-clearing, scoring, hold, preview, shadow, and
//! wall-kick are all reached through `self.s6` — only the garbage-
//! materialization logic, the multiplayer bookkeeping, and the three
//! `receive_*` methods are genuinely new here. See `implementation.md` §4–§8.
//!
//! Two deviations from `implementation.md`'s own pseudocode, needed for this
//! file to actually compile against the crates as generated:
//!
//! - **§6.9/§6.10 reach `t5::model::{check_axioms, check_invariants}`
//!   directly, not `t6::model`'s.** `t6::model::Machine<P>` is a type alias
//!   for `t5::model::Machine<P>` and re-exports neither checker; `t6`'s own
//!   `tests/oracle.rs` reaches `t5::model::check_invariants` for the same
//!   reason.
//! - **§0.1/§11's `CellExtra = Garbage` pinning is done here, on
//!   `t7::model::Params` itself, not in `instance.rs`.** `fill_garbage_row`
//!   needs to construct a concrete `P::CellExtra` value naming the garbage
//!   marker, well-typed only if every `P: Params` is known to have
//!   `CellExtra = Garbage`; `instance.rs` need only write
//!   `type CellExtra = crate::model::Garbage;` against this bound.

use t6::model::T6MachineExt as _;

// ── Invariant checker flags ──────────────────────────────────────────────
pub const CHECK_AXIOMS: bool = true;
pub const CHECK_INVARIANTS: bool = false;

// ── Garbage: the reserved "not a real piece" mg cell content ────────────

/// No `T7.v` counterpart (§11) — unit-valued, since a garbage cell carries
/// no further information to render (unlike a real `Piece`). See this
/// module's own header comment for why it lives here, not in `instance.rs`.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct Garbage;

// ── Params: T7.v's new parameters are runtime roster facts, not Params items ──

/// spec: `T7.v`'s new `Parameter`s (`Player`, `Host`, `PlayerEqb`,
/// `PlayerNext`, `PlayerCount`) are runtime roster facts, not `Params`
/// items (§0.2) — none are named here; they're plain runtime values
/// threaded through `Machine::new` and the lobby protocol (§6.1, §15).
///
/// The one thing this trait adds: pinning `CellExtra = Garbage` (module
/// header). `t1::model::Params` is named explicitly, alongside the
/// `t6::model::Params` supertrait, because an associated-type binding in
/// supertrait position only applies to the trait that declares the item.
pub trait Params: t6::model::Params + t1::model::Params<CellExtra = Garbage> {}

// ── Free functions (T7.v source order, §5) ───────────────────────────────

/// spec: PlayingView s pl1 pl2, with `pl1` implicit — a `Machine` only ever
/// evaluates its own views (§0.2), so this takes the view arrays directly
/// rather than an observer index.
pub fn playing_view(gameover_view: &[bool], connected_view: &[bool], pl2: usize) -> bool {
    !gameover_view[pl2] && connected_view[pl2]
}

/// spec: WinnerMulti s pl. `1 <? PlayerCount` is not checked here —
/// `Machine::new` asserts `player_count > 1` once, at construction
/// (`implementation.md` §0.2, §6.1), so every `gameover_view`/
/// `connected_view` this function ever sees already satisfies it.
pub fn winner_multi(gameover_view: &[bool], connected_view: &[bool], my_index: usize) -> bool {
    (0..gameover_view.len())
        .all(|pl2| playing_view(gameover_view, connected_view, pl2) == (pl2 == my_index))
}

/// spec: NextTargetAux / NextTarget — fuel-bounded loop, `player_count`
/// fuel, the same "`Fixpoint` on a strictly-decreasing measure → loop with
/// an explicit fuel count" idiom `t5::model`'s own `shadow_y` already uses
/// (`implementation.md` §3). Returns `self_` if no candidate is found
/// within one full cycle (the winner case — req-multi-target-nonself).
pub fn next_target(
    playing: impl Fn(usize) -> bool,
    self_: usize,
    pl: usize,
    player_count: usize,
) -> usize {
    let mut cur = pl;
    for _ in 0..player_count {
        cur = (cur + 1) % player_count;
        if playing(cur) && cur != self_ {
            return cur;
        }
    }
    self_
}

/// spec: GeneratedGarbage — req-multi-garbage-gen
pub fn generated_garbage(cleared_lines: i64, perfect_clear: bool) -> i64 {
    let normal = if cleared_lines < 4 {
        cleared_lines - 1
    } else {
        cleared_lines
    };
    let normal = normal.max(0); // natural subtraction: `c - 1` at `c = 0` must floor at 0
    let special = if perfect_clear { 10 } else { 0 };
    normal + special
}

/// spec: GenRemGarbage — (genGarbage, remGarbage). `remGarbage` materializes
/// onto this player's own board; the generated half is sent onward to the
/// target. At most one is ever nonzero, by construction (§4-T7b).
pub fn gen_rem_garbage(garbage: i64, cleared_lines: i64, perfect_clear: bool) -> (i64, i64) {
    let gen_garbage = generated_garbage(cleared_lines, perfect_clear);
    let rem_garbage = (garbage - gen_garbage).max(0); // req-multi-garbage-cancel
    (gen_garbage, rem_garbage)
}

/// spec: `GarbageGrid`'s per-row content — folded into `fix_piece`'s
/// materialization rather than emitted as its own grid value (§4-T7c′).
/// Writes into an existing row in place, reusing its allocation (board
/// width never changes) instead of collecting a fresh `Vec`.
fn fill_garbage_row<P: Params>(row: &mut [Option<t1::model::PieceOrExtra<P>>], hole: i64) {
    let w = row.len() as i64;
    assert!(
        0 <= hole && hole < w,
        "ValidHoles: hole {hole} outside [0, {w})"
    ); // spec: ValidHoles
    for (x, cell) in row.iter_mut().enumerate() {
        *cell = if x as i64 == hole {
            None
        } else {
            Some(t1::model::PieceOrExtra::Extra(Garbage))
        };
    }
}

// ── Machine: T7.State's per-player local half ────────────────────────────

/// spec: State, restricted to what is local to one player (§1) —
/// `connected`/`messages` are not fields anywhere in this module; they are
/// realized entirely in `net.rs` (§0.4, §15).
pub struct Machine<P: Params> {
    pub s6: t6::model::Machine<P>, // spec: s6
    pub my_index: usize,
    pub garbage: i64,              // spec: garbage — received pending garbage
    pub target: usize,             // spec: target
    pub gameover_view: Vec<bool>,  // spec: gameoverView — own view only, len = player_count
    pub connected_view: Vec<bool>, // spec: connectedView — own view only
    pub rem_gen_garbage: i64,      // spec: FP.RemGenGarbage — read by the caller after fix_piece
}

impl<P: Params> Machine<P> {
    /// spec: Init. `player_count > 1` and `my_index < player_count` are
    /// asserted here, once, at the point the roster is frozen — the
    /// closest Rust analogue to `PlayerCountPositive` (§0.2: not a
    /// `check_axioms::<P>()` conjunct, since neither value is a `Params`
    /// item).
    pub fn new(
        my_index: usize,
        player_count: usize,
        bags_fn: impl FnMut(u64) -> Vec<P::Piece>,
        piece_source: impl FnMut() -> P::Piece,
    ) -> Self {
        assert!(
            player_count > 1,
            "T7::Machine is for multiplayer only — single-player uses t6::model::Machine directly"
        );
        assert!(my_index < player_count);
        let s6 = t6::model::Machine::new(bags_fn, piece_source); // spec: s6Init pl := T6.Init (bags pl) (H pl)
        let mut gameover_view = vec![false; player_count];
        gameover_view[my_index] = s6.gameover(); // spec: Init's gameoverView (obsd=obs case)
        let m = Machine {
            s6,
            garbage: 0,
            target: (my_index + 1) % player_count, // spec: target := PlayerNext
            gameover_view,
            connected_view: vec![true; player_count], // spec: connectedView := PlayerCount>1 (asserted true)
            rem_gen_garbage: 0,
            my_index,
        };
        if CHECK_INVARIANTS {
            check_invariants(&m);
        }
        m
    }

    /// spec: MovePiece — full use (`implementation.md` §1): guard, then a
    /// one-line delegating call to `self.s6`'s own method.
    pub fn move_piece(&mut self, dy: i64, dx: i64) -> bool {
        if winner_multi(&self.gameover_view, &self.connected_view, self.my_index) {
            return false;
        }
        let fired = self.s6.move_piece(dy, dx);
        if CHECK_INVARIANTS {
            check_invariants(self);
        }
        fired
    }

    /// spec: RotatePiece — full use, same shape as `move_piece`.
    pub fn rotate_piece(&mut self, cw: bool) -> bool {
        if winner_multi(&self.gameover_view, &self.connected_view, self.my_index) {
            return false;
        }
        let fired = self.s6.rotate_piece(cw);
        if CHECK_INVARIANTS {
            check_invariants(self);
        }
        fired
    }

    /// spec: HoldPiece — full use, same shape as `move_piece`.
    pub fn hold_piece(&mut self, bag_new: &[P::Piece]) -> bool {
        if winner_multi(&self.gameover_view, &self.connected_view, self.my_index) {
            return false;
        }
        let fired = self.s6.hold_piece(bag_new);
        if CHECK_INVARIANTS {
            check_invariants(self);
        }
        fired
    }

    /// spec: RotateKickPiece — full use, same shape as `move_piece`.
    /// `t6::model::RotateKickPieceExt` is imported at this module's top
    /// (`use ... as _`) so `self.s6.rotate_kick_piece(cw)` resolves.
    pub fn rotate_kick_piece(&mut self, cw: bool) -> bool {
        if winner_multi(&self.gameover_view, &self.connected_view, self.my_index) {
            return false;
        }
        let fired = self.s6.rotate_kick_piece(cw);
        if CHECK_INVARIANTS {
            check_invariants(self);
        }
        fired
    }

    /// spec: FixPiece — `implementation.md` §4-T7a–§4-T7d, §6.3. `holes` is
    /// passed fresh by the caller, never persisted on `Machine`.
    pub fn fix_piece(&mut self, bag_new: &[P::Piece], holes: impl Fn(i64) -> i64) -> bool {
        if winner_multi(&self.gameover_view, &self.connected_view, self.my_index) {
            return false;
        }
        if !self.s6.fix_piece(bag_new) {
            return false; // T6's own guard failed — matches option_map's None case, zero mutation below
        }
        // Materialization always proceeds from here — no `player_count = 1`
        // branch anywhere in this module (`implementation.md` §4-T7a):
        // single-player mode never constructs a `t7::model::Machine` at all.

        let cleared_lines = self.s6.cleared_lines();
        let perfect_clear = self.s6.perfect_clear();
        let (gen_garbage, rem_garbage) =
            gen_rem_garbage(self.garbage, cleared_lines, perfect_clear);
        self.rem_gen_garbage = (gen_garbage - self.garbage).max(0); // spec: FP.RemGenGarbage

        let hm = self.s6.mg().len() as i64;
        let wm = self.s6.mg()[0].len() as i64;
        let eff_rem = rem_garbage.min(hm); // remGarbage is unbounded; clamp for array indices

        let mut gameover2 = self.s6.gameover();
        if !gameover2 && rem_garbage > 0 {
            gameover2 = if rem_garbage >= hm {
                true // pushes the entire board off — no scan needed
            } else {
                // must read the top rows BEFORE the shift below overwrites them
                (hm - rem_garbage..hm)
                    .any(|y| (0..wm).any(|x| self.s6.mg()[y as usize][x as usize].is_some()))
            };
        }

        // shift always runs, regardless of gameover2 — the stored grid always
        // reflects materialization, whatever caused gameover2.
        if eff_rem > 0 {
            // rotate_right(eff_rem) moves the top eff_rem rows to the front
            // (about to be overwritten below) and shifts the rest up by
            // eff_rem — same shift semantics as a clone loop, but moves Vec
            // handles instead of cloning row contents: 0 allocation.
            self.s6.mg_mut().rotate_right(eff_rem as usize);
            for y in 0..eff_rem {
                fill_garbage_row::<P>(&mut self.s6.mg_mut()[y as usize], holes(y));
            }
            self.s6.update_shadow_y(); // the freshly-spawned piece's shadow is now stale
        }

        if !gameover2 {
            gameover2 = t1::model::intersect(P::forbidden_grid(), P::FY, P::FX, self.s6.mg(), 0, 0);
        }
        *self.s6.gameover_mut() = gameover2;

        self.gameover_view[self.my_index] = gameover2; // SelfViewAccurate
        if self.rem_gen_garbage > 0 && !gameover2 {
            // §4-T7e′'s from-exclusion isn't needed here — next_target's own
            // `pl2 != self` check already rejects `self.my_index` as a
            // candidate regardless of what playing_view says about it.
            self.target = next_target(
                |pl2| playing_view(&self.gameover_view, &self.connected_view, pl2),
                self.my_index,
                self.target,
                self.gameover_view.len(),
            );
        }
        self.garbage = 0; // consumed by materialization; the target is credited on delivery (receive_garbage)

        if CHECK_INVARIANTS {
            check_invariants(self);
        }
        true
    }

    /// spec: FallStep. Disjoint-guard sequencing, as every prior layer's own
    /// `fall_step` — no guard of its own, both branches already run one.
    pub fn fall_step(&mut self, bag_new: &[P::Piece], holes: impl Fn(i64) -> i64) -> bool {
        if self.move_piece(-1, 0) {
            return true;
        }
        self.fix_piece(bag_new, holes)
    }

    /// spec: DropPiece — req-piece-drop. An explicit `winner_multi` guard is
    /// required *before* the relocation below (§4-T7h): Rust's in-place
    /// mutation would otherwise commit a `WinnerMulti` player's relocation
    /// before the trailing `fix_piece` call rejects it.
    pub fn drop_piece(&mut self, bag_new: &[P::Piece], holes: impl Fn(i64) -> i64) -> bool {
        if winner_multi(&self.gameover_view, &self.connected_view, self.my_index) {
            return false; // guards the relocation below, not just the trailing fix
        }
        let gy = self.s6.gy;
        let px = self.s6.px();
        t1::model::new_piece_yx_state::<P>(gy, px, self.s6.s1_mut()); // spec: NewPieceYXState
        self.fix_piece(bag_new, holes) // re-checks winner_multi, harmlessly redundant
    }

    /// spec: NoticeDisconnection — called on locally detecting the link to the
    /// host has failed. Flips `self.connected_view[self.my_index]` only,
    /// idempotently — the `connected s pl` half of `T7.v`'s own guard is the
    /// caller's responsibility (`implementation.md` §0.1); only the "have I not
    /// already noticed" half is checkable inside `Machine`.
    pub fn notice_disconnection(&mut self) -> bool {
        if !self.connected_view[self.my_index] {
            return false; // already noticed — idempotent
        }
        self.connected_view[self.my_index] = false;
        true
    }

    /// spec: ReceiveMessage — GarbageMessage branch. Sender-agnostic `+=`,
    /// no `from`. Not gated on `winner_multi`/`gameover`: a disconnected/
    /// gameover player keeps draining her queues; the value simply sits
    /// inert (never read again, since she can never fix again).
    pub fn receive_garbage(&mut self, amount: i64) {
        self.garbage += amount; // spec: garbage[pl] += n
    }

    /// spec: ReceiveMessage — GameoverMessage branch.
    pub fn receive_gameover(&mut self, from: usize) {
        if self.target == from {
            self.target = self.redirect_target_from(from);
        }
        self.gameover_view[from] = true;
    }

    /// spec: ReceiveMessage — DisconnectMessage branch. Same target
    /// redirect as the gameover branch (`T7.v` uses one shared `view'` for
    /// both).
    pub fn receive_disconnect(&mut self, from: usize) {
        if self.target == from {
            self.target = self.redirect_target_from(from);
        }
        self.connected_view[from] = false;
    }

    /// spec: the shared `view'`/`PlayingView'` closure `ReceiveMessage`'s
    /// gameover/disconnect branches use for their target redirect (§4-T7e′):
    /// `T7.v` computes `target` and the view field as simultaneous updates
    /// from the same pre-state, so this closure carries the `from`-exclusion
    /// explicitly rather than relying on an update-ordering argument.
    fn redirect_target_from(&self, from: usize) -> usize {
        let (gameover_view, connected_view) = (&self.gameover_view, &self.connected_view);
        next_target(
            |pl2| {
                if pl2 == from {
                    false
                } else {
                    playing_view(gameover_view, connected_view, pl2)
                }
            },
            self.my_index,
            from,
            gameover_view.len(),
        )
    }
}

// ── Axiom/invariants checker ─────────────────────────────────────────────

/// spec: `T7.v`'s own axiom (`PlayerCountPositive`) is not a `Params`-level
/// fact (§0.2) — checked instead as a runtime assertion in `Machine::new`.
/// Pure delegation here, to `t5::model::check_axioms` (this module's own
/// header comment explains the `t6::model` deviation).
pub fn check_axioms<P: Params>() {
    t5::model::check_axioms::<P>();
}

/// Layered on `t5::model::check_invariants`; the only conjunct this layer
/// adds beyond delegation is `SelfViewAccurate` — checked here since this
/// is the one layer that actually stores a `gameover_view` to check it
/// against.
pub fn check_invariants<P: Params>(s: &Machine<P>) {
    t5::model::check_invariants(&s.s6);
    let n = s.gameover_view.len();
    assert!(s.garbage >= 0);
    assert!(s.target < n);
    assert_eq!(s.connected_view.len(), n);
    assert_eq!(
        s.gameover_view[s.my_index],
        s.s6.gameover(),
        "SelfViewAccurate"
    );
    // TargetNotSelf / TargetPlaying (T7.v) both hold only under NoWinner
    // (T7.v:623), which reads the true state of every player — a fact this
    // single-player Machine structurally cannot observe (it only ever holds
    // my_index's own, possibly-stale view of others). No sound local proxy
    // exists; left to proofs.md, as rs/t7/implementation.md already does.
}
