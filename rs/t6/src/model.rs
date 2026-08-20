//! spec: T6
//!
//! The T6 engine: `T5.v` plus wall-kick rotation. §1: `Machine<P>` is a
//! type alias for `t5::model::Machine<P>`, not a wrapping struct — the
//! new `rotate_kick_piece` method is added via an extension trait
//! instead. See `implementation.md` §4–§8.

// ── Params: T6.v adds no new abstract parameter ─────────────────────────────

/// spec: §6.0 — no new `Params` trait; a vacuous wrapper would be dead
/// indirection.
pub use t5::model::Params;

// ── Machine: T6.State = T5.State ─────────────────────────────────────────────

/// spec: State (`= T5.State`)
pub type Machine<P> = t5::model::Machine<P>;

// ── RotateKickPieceExt: the sole new action ─────────────────────────────────

/// spec: §1 — extension trait, since `Machine<P>` is a foreign type here
/// and Rust forbids an inherent impl on it.
pub trait T6MachineExt<P: Params> {
    fn rotate_kick_piece(&mut self, cw: bool) -> bool;
    fn mg(&self) -> &Vec<Vec<Option<t1::model::PieceOrExtra<P>>>>;
    fn mg_mut(&mut self) -> &mut Vec<Vec<Option<t1::model::PieceOrExtra<P>>>>;
    fn px(&self) -> i64;
    fn gameover(&self) -> bool;
    fn gameover_mut(&mut self) -> &mut bool;
    fn cleared_lines(&self) -> i64;
    fn perfect_clear(&self) -> bool;
    fn s1_mut(&mut self) -> &mut t1::model::Machine<P>;
}

impl<P: Params> T6MachineExt<P> for Machine<P> {
    /// spec: RotateKickPiece — req-piece-kick, §4-T6b.
    fn rotate_kick_piece(&mut self, cw: bool) -> bool {
        let s1 = &self.s4.s3.s2.s1;
        if s1.gameover || t1::model::can_rotate_piece::<P>(cw, s1) {
            return false; // exclusive with a plain rotation that would fire
        }
        let (orig_py, orig_px) = (s1.py, s1.px);

        // spec: T5.RotatePiece clockwise (T5.NewPieceYXState (py s, px s - 1) s) — left
        t1::model::new_piece_yx_state::<P>(orig_py, orig_px - 1, &mut self.s4.s3.s2.s1);
        let mut fired = self.rotate_piece(cw); // reuse — full use

        if !fired {
            // spec: T5.RotatePiece clockwise (T5.NewPieceYXState (py s, px s + 1) s) — right,
            // relative to the ORIGINAL px, not the failed left attempt
            t1::model::new_piece_yx_state::<P>(orig_py, orig_px + 1, &mut self.s4.s3.s2.s1);
            fired = self.rotate_piece(cw);
        }

        if !fired {
            // both kicks failed: restore (§4-T6b — px is a trivially-restorable scalar)
            t1::model::new_piece_yx_state::<P>(orig_py, orig_px, &mut self.s4.s3.s2.s1);
        }

        if t5::model::CHECK_INVARIANTS {
            t5::model::check_invariants(self); // T6.Correct = T5.Correct — not redefined
        }
        fired
    }

    fn mg(&self) -> &Vec<Vec<Option<t1::model::PieceOrExtra<P>>>> {
        &self.s4.s3.s2.s1.mg
    }

    fn mg_mut(&mut self) -> &mut Vec<Vec<Option<t1::model::PieceOrExtra<P>>>> {
        &mut self.s4.s3.s2.s1.mg
    }

    fn px(&self) -> i64 {
        self.s4.s3.s2.s1.px
    }

    fn gameover(&self) -> bool {
        self.s4.s3.s2.s1.gameover
    }

    fn gameover_mut(&mut self) -> &mut bool {
        &mut self.s4.s3.s2.s1.gameover
    }

    fn cleared_lines(&self) -> i64 {
        self.s4.s3.s2.s1.cleared_lines
    }

    fn perfect_clear(&self) -> bool {
        self.s4.s3.s2.perfect_clear
    }

    fn s1_mut(&mut self) -> &mut t1::model::Machine<P> {
        &mut self.s4.s3.s2.s1
    }
}
