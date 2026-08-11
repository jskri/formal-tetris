(***************************************************************************
This model extends T4 with the piece drop mechanics.


# New addressed requirements

req-piece-drop, req-piece-shadow

(see definitions_requirements.md)


# Design

The location of the shadow (aka ghost) of the current piece could be computed
externally, by using the current piece position, rotation and the main grid.
However, it is more convenient that T5 provides it. T5 provides only the y of
the shadow, since its x and rotation are the same as the current piece.


# Invariants

State invariants ensure the shadow is at its lowest position starting from its
initial position (see `LowestShadowY`).


# Refinement

The piece drop is genuinely new: it has no counterpart in T4 and any T5
behavior that contains a piece drop cannot be mapped to a T4 behavior. However,
T5 minus piece drop does refine T4: the only added field, the ghost y, is
completely orthogonal to T4.

 ***************************************************************************)

From Tetris Require T4.
Import T1(Piece, PW, Grid, Valid).
Import T4(py, px, pr, p, mg).
From Tetris Require Import Notations.


(* ========================================================================= *)
(* Specification                                                             *)
(* ========================================================================= *)

Record State := mkState
  { s4 : T4.State
  ; gy : ℤ  (* y of the ghost/shadow of the current piece *)
  }.

Fixpoint ShadowYImpl (fuel : ℕ) (mg : Grid) (p : Piece) (py px pr : ℤ) : ℤ :=
  match fuel with
  | O => py
  | S fuel' =>
      if ! (Valid mg p (py - 1, px) pr) then
        py
      else
        ShadowYImpl fuel' mg p (py - 1) px pr
  end.

(* fuel takes into account the fact that py can go below 0, as long as *occupied
   cells* are inside the main grid. *)
Definition ShadowY (s4 : T4.State) : ℤ :=
  let fuel := (Z.to_nat (py s4) + Z.to_nat PW - 1)%nat in
  ShadowYImpl fuel (mg s4) (p s4) (py s4) (px s4) (pr s4).

Definition Init (bags : ℕ → ℕ → Piece) (H : ∀ i, T4.PieceSet (bags i)) : State :=
  let s4 := T4.Init bags H in
  {| s4 := s4
  ;  gy := ShadowY s4
  |}.

Inductive Event :=
  | Event4 (e4 : T4.Event)
  | Drop (bagNew : ℕ → Piece) (H : T4.PieceSet bagNew).

Definition UnchangedT5Part (s : State) (s4 : T4.State) : State :=
  {| s4 := s4
  ;  gy := gy s (* unchanged *)
  |}.

Definition UpdateShadowY (s : State) (s4 : T4.State) : State :=
  {| s4 := s4
  ;  gy := ShadowY s4
  |}.

(* Forward to T4. *)
Definition MovePiece (dyx : ℤ × ℤ) (s : State) : option State :=
  option_map (UpdateShadowY s) (T4.MovePiece dyx (s4 s)).

(* Forward to T4. *)
Definition RotatePiece (clockwise : bool) (s : State) : option State :=
  option_map (UpdateShadowY s) (T4.RotatePiece clockwise (s4 s)).

(* Forward to T4. *)
Definition FixPiece (bagNew : ℕ → Piece) (H : T4.PieceSet bagNew) (s : State)
    : option State :=
  option_map (UpdateShadowY s) (T4.FixPiece bagNew H (s4 s)).

Definition FallStep (bagNew : ℕ → Piece) (H : T4.PieceSet bagNew) (s : State)
    : option State :=
  (* option_map (UpdateShadowY s) (T4.FallStep bagNew H (s4 s)). *)
  match MovePiece (-1, 0) s with
  | Some s' => Some s'
  | None    => FixPiece bagNew H s
  end.

(* Forward to T4. *)
Definition HoldPiece (bagNew : ℕ → Piece) (H : T4.PieceSet bagNew) (s : State)
    : option State :=
  option_map (UpdateShadowY s) (T4.HoldPiece bagNew H (s4 s)).

Definition NewPieceYXState (pyxNew : ℤ × ℤ) (s5 : State) : State :=
  let s4 := T5.s4 s5 in
  let s3 := T4.s3 s4 in
  let s2 := T3.s2 s3 in
  let s1 := T2.s1 s2 in
  T5.UnchangedT5Part s5
    (T4.UnchangedT4Part s4
      (T3.UnchangedT3Part s3
        (T2.UnchangedT2Part s2
          (T1.NewPieceYXState pyxNew s1)))).

Definition mg (s : State) : Grid := T4.mg (s4 s).
Definition p (s : State) : Piece := T4.p (s4 s).
Definition py (s : State) : ℤ := T4.py (s4 s).
Definition px (s : State) : ℤ := T4.px (s4 s).
Definition pr (s : State) : ℤ := T4.pr (s4 s).
Definition gameover (s : State) : bool := T4.gameover (s4 s).
Definition clearedLines (s : State) : ℕ := T4.clearedLines (s4 s).
Definition score (s : State) : ℕ := T4.score (s4 s).
Definition level (s : State) : ℕ := T4.level (s4 s).
Definition hold (s : State) : option Piece := T4.hold (s4 s).

Definition DropPiece (bagNew : ℕ → Piece) (H : T4.PieceSet bagNew) (s : State)
    : option State :=
  FixPiece bagNew H (NewPieceYXState (gy s, px s) s).

(* Next without Drop *)
Definition NextT4Event (e : T4.Event) (s : State) : option State :=
  match e with
  | T4.Move dyx      => MovePiece dyx s
  | T4.Rotate cw     => RotatePiece cw s
  | T4.Fix bagNew H  => FixPiece bagNew H s
  | T4.Fall bagNew H => FallStep bagNew H s
  | T4.Hold bagNew H => HoldPiece bagNew H s
  | T4.Stutter       => Some s
  end.

Definition Next (e : Event) (s : State) : option State :=
  match e with
  | Event4 e4 => NextT4Event e4 s
  | Drop bagNew H => DropPiece bagNew H s
  end.


(* ========================================================================= *)
(* State invariants                                                          *)
(* ========================================================================= *)

Definition ValidPieceCannotGoDown (s : State) (py : ℤ) : Prop :=
    Valid (mg s) (p s) (py, px s) (pr s) = true
  ∧ Valid (mg s) (p s) (py - 1, px s) (pr s) = false.

Definition LowestShadowY (s : State) : Prop :=
  gameover s = false →
    gy s ≤ py s
  ∧ ValidPieceCannotGoDown s (gy s)
  ∧ ∀ y, y ≤ py s → ValidPieceCannotGoDown s y → y ≤ gy s.

Definition GyEqShadowY (s : State) : Prop :=
  gy s = ShadowY (s4 s).

Definition Correct (s : State) : Prop :=
    T4.Correct (s4 s)
  ∧ LowestShadowY s
  ∧ GyEqShadowY s.


(* ========================================================================= *)
(* Step invariants                                                           *)
(* ========================================================================= *)

Definition CorrectStep (s s' : State) : Prop :=
  T4.CorrectStep (s4 s) (s4 s').


(* ========================================================================= *)
(* Refinement                                                                *)
(* ========================================================================= *)

(* The refinement holds only when excluding Drop, i.e. it holds on T4 events. *)

(* Define the refinement mapping f with its event component and its
   state component. *)

(* Event component: identity function *)
Definition fₑ : T4.Event → T4.Event :=
  id.

(* State component: projection to T2.State *)
Definition fₛ: T5.State → T4.State :=
  s4.

(*
For T4 refinement to hold, this diagram must commute:
         e4
   s4    →    s4'
fₛ ↑     ⇑fₑ  ↑ fₛ
   s5    →    s5'
         e5
*)

Definition T4RefinesT5 : Prop :=
    (∀ bags HSet, fₛ (T5.Init bags HSet) = T4.Init bags HSet)
  ∧ (∀ e4 s5 s5'
     (H1 : GyEqShadowY s5)
     (H2 : NextT4Event e4 s5 = Some s5'),
     T4.Next (fₑ e4) (fₛ s5) = Some (fₛ s5')).


(* ========================================================================= *)
(* Helpers for refining models                                               *)
(* ========================================================================= *)

Definition perfectClear (s : State) : bool := T4.perfectClear (s4 s).

Definition CorrectWithoutGameover (s : State) : Prop :=
    T4.CorrectWithoutGameover (s4 s)
  ∧ LowestShadowY s
  ∧ GyEqShadowY s.

Definition pyx (s : State) : ℤ × ℤ :=
  T1.pyx (T2.s1 (T3.s2 (T4.s3 (s4 s)))).

(* Definition clearedLines (s : State) : ℤ × ℤ :=
  T1.clearedLines (T2.s1 (T3.s2 (T4.s3 (s4 s)))). *)

Definition combo s := T2.combo (T3.s2 (T4.s3 (s4 s))).
Definition totalClearedLines s := T2.totalClearedLines (T3.s2 (T4.s3 (s4 s))).
Definition swapped s := T3.swapped (T4.s3 (s4 s)).
Definition d s := T4.d (s4 s).