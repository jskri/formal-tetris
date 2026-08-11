(***************************************************************************
This model extends T5 with the wall kick mechanics.


# New addressed requirements

req-piece-kick

(see definitions_requirements.md)


# Design

When the piece is too close to an obstacle to rotate, it is pushed away to
allow rotation, first one block on the left, then one block on the right.

To make refinement easier to express, `RotatePiece` is not updated with
wall kick rotations, but a new `RotateKickPiece` event is added, which can
trigger only if `RotatePiece` cannot. `RotateKickPiece` then reuses
`RotatePiece`.

This makes T6 a pure addition on top of T5: one new event, no new field, and
existing events reused as-is. Since the state has no new field, T5.State is
reused directly.


# Refinement

The wall kick mechanics is genuinely new: it has no counterpart in T5 and any T6
behavior that contains a wall kick cannot be mapped to a T5 behavior. However,
T6 minus wall kick does refine T5, since the state and the remaining events are
the same.

***************************************************************************)

From Tetris Require T5.
Export T5(mg, py, px, gameover).
From Tetris Require Import Notations.


(* ========================================================================= *)
(* Specification                                                             *)
(* ========================================================================= *)

(* No new state fields. *)
Definition State := T5.State.

Definition Init := T5.Init.

(* The sole new event, exclusive with T5.RotatePiece:
- if rotation is impossible, move piece to the left
- if rotation is still impossible, move piece to the right
*)
Definition RotateKickPiece (clockwise : bool) (s : State) : option State :=
  (* Reuse the if-guard-then-body-else-none pattern from previous models. *)
  let plainRotFires :=
    match T5.RotatePiece clockwise s with Some _ => true | None => false end in
  (* Is there `isSome isNone : option A → bool` in Rocq? *)
  if (! gameover s) && (! plainRotFires) then
    match T5.RotatePiece clockwise (T5.NewPieceYXState (py s, px s - 1) s) with (* left *)
    | Some s => Some s
    | None => T5.RotatePiece clockwise (T5.NewPieceYXState (py s, px s + 1) s) (* right *)
    end
  else
    None.

Inductive Event :=
  | Event5 (e5 : T5.Event)
  | RotateKick (cw : bool).

(* Next without RotateKick *)
Definition NextT5Event (e5 : T5.Event) (s : State) : option State :=
  T5.Next e5 s.

Definition Next (e : Event) (s : State) : option State :=
  match e with
  | Event5 e5 => NextT5Event e5 s
  | RotateKick cw => RotateKickPiece cw s
  end.


(* ========================================================================= *)
(* State invariants                                                          *)
(* ========================================================================= *)

(* No new state invariant. T5.Correct must also hold of RotateKickPiece. *)
Definition Correct (s : State) : Prop :=
  T5.Correct s.


(* ========================================================================= *)
(* Step invariants                                                           *)
(* ========================================================================= *)

Definition CorrectStep (s s' : State) : Prop :=
  T5.CorrectStep s s'.


(* ========================================================================= *)
(* Refinement                                                                *)
(* ========================================================================= *)

(* The refinement holds only when excluding RotateKick, i.e. it holds on T5
events. *)

(* Event component: identity function *)
Definition fₑ : T5.Event → T5.Event :=
  id.

(* State component: identity function *)
Definition fₛ: T6.State → T6.State :=
  id.

(*
For T5 refinement to hold, this diagram must commute:
         e5
   s5    →    s5'
fₛ ↑     ⇑fₑ  ↑ fₛ
   s6    →    s6'
         e5
*)

Definition T6RefinesT5 : Prop :=
    (∀ bags HSet, fₛ (T6.Init bags HSet) = T5.Init bags HSet)
  ∧ (∀ e5 s6 s6'
     (H1 : NextT5Event e5 s6 = Some s6'),
     T6.NextT5Event (fₑ e5) (fₛ s6) = Some (fₛ s6')).


(* ========================================================================= *)
(* Helpers for refining models                                               *)
(* ========================================================================= *)

Definition s5 : T6.State → T5.State := id.
Definition MovePiece := T5.MovePiece.
Definition RotatePiece := T5.RotatePiece.
Definition FixPiece := T5.FixPiece.
Definition HoldPiece := T5.HoldPiece.

Definition mg := T5.mg.
Definition p := T5.p.
Definition pyx := T5.pyx.
Definition pr := T5.pr.
Definition gameover := T5.gameover.
Definition clearedLines := T5.clearedLines.
Definition score := T5.score.
Definition level := T5.level.
Definition combo := T5.combo.
Definition perfectClear := T5.perfectClear.
Definition totalClearedLines := T5.totalClearedLines.
Definition hold := T5.hold.
Definition swapped := T5.swapped.
Definition d := T5.d.
Definition gy := T5.gy.

Definition px := T5.px.
Definition UnchangedT6Part (_ : T6.State) : T5.State → T6.State := id.
Definition NewPieceYXState := T5.NewPieceYXState.
Definition CorrectWithoutGameover := T5.CorrectWithoutGameover.
