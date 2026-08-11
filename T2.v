(***************************************************************************
This model extends T1 with score/level mechanics.


# New addressed requirements

req-score, req-score-init, req-score-formula, req-level, req-level-init,
req-level-formula

(see definitions_requirements.md)


# Design

This model does not add new events; it only enriches existing events in an
orthogonal way by computing the score and level.

Each T2 state embeds a T1 state (see `State`).


# Invariants

In addition to state invariants, this model defines step invariants, properties
that hold for a pair of states (s, s'), where s' is a direct successor of s:

- score and level do not decrease (`NonDecreasingScore`, `NonDecreasingLevel`)

- score rises on line clear


# Refinement

T2 obviously refines T1 if we forget the new T2 fields (see `fₛ`).

In the other direction, i.e. from T1 to T2, no refinement exists in the same
sense because the score/level data is missing in T1. However, it is possible to
show that T2 allows all behaviors that T1 does. Indeed, `fₛ : T2.State →
T1.State` is surjective on reachable states and admits a deterministic section
that adds the new T2 fields. Note that this section is a function of T1 traces
(i.e. a sequence of T1 events), not of T1 states. This is because the new T2
fields can only be computed inductively from the initial states.

***************************************************************************)

From Stdlib Require Import List. (* for forallb *)
From Tetris Require T1.
Export T1(Piece, Grid, L, H, W, mg, p, pr, py, px, gameover, clearedLines).
From Tetris Require Import Notations Quantifiers.
Open Scope nat_scope.
Import ListNotations.

(* ========================================================================= *)
(* Specification                                                             *)
(* ========================================================================= *)

Record State := mkState
  { s1 : T1.State
  ; score : ℕ
  ; level : ℕ
  ; combo : ℕ
  ; perfectClear : bool
  ; totalClearedLines : ℕ
  }.

Definition Init (p : Piece) : State :=
  {| s1 := T1.Init p
  ;  score := 0 (* req-score-init *)
  ;  level := 1 (* req-level-init *)
  ;  combo := 0
  ;  perfectClear := false
  ;  totalClearedLines := 0
  |}.

(* Same events as T1. *)
Inductive Event :=
  | Move    (dyx  : ℤ × ℤ)
  | Rotate  (cw   : bool)
  | Fix     (pNew : Piece)
  | Fall    (pNew : Piece)
  | Stutter.

(***************************************************************************
The move, rotation and fall step of a piece are unchanged. FallStep requires
the definition of FixPiece, so it is placed after.
 ***************************************************************************)

(* Update the T1 part of s, if possible. *)
Definition UpdateS1 (optT1 : option T1.State) (s : State) : option State :=
  option_map
    (λ s1, {| s1 := s1
           ;  score := score s
           ;  level := level s
           ;  combo := combo s
           ;  perfectClear := perfectClear s
           ;  totalClearedLines := totalClearedLines s
           |})
    optT1.

Definition MovePiece (dyx : ℤ × ℤ) (s : State) : option State :=
  UpdateS1 (T1.MovePiece dyx (s1 s)) s.

Definition RotatePiece (clockwise : bool) (s : State) : option State :=
  UpdateS1 (T1.RotatePiece clockwise (s1 s)) s.

(***************************************************************************
However, the fixation of a piece does change since score and level update
occurs then.

We define the different sources of points: clearing lines,
making combos and making perfect clears.
 ***************************************************************************)

Definition LineClearPoints (clearedLines level : ℕ) : ℕ :=
  match clearedLines with
  | 0 =>   0
  | 1 => 100 * level
  | 2 => 300 * level
  | 3 => 500 * level
  | _ => 800 * level
  end.

Definition ComboPoints (level combo : ℕ) : ℕ :=
  if 0 <? combo then (50 * combo * level) else 0.

Definition PerfectClearPoints (perfectClear : bool) (clearedLines level : ℕ) : ℕ :=
  if negb perfectClear
  then 0
  else match clearedLines with
       | 0 =>    0
       | 1 =>  800 * level
       | 2 => 1200 * level
       | 3 => 1800 * level
       | _ => 2000 * level
       end.

(* req-score-formula *)
Definition Points (clearedLines level combo : ℕ) (perfectClear : bool) : ℕ :=
    (LineClearPoints clearedLines level)
  + (ComboPoints level combo)
  + (PerfectClearPoints perfectClear clearedLines level).

Definition EmptyGridb (g : Grid) : bool :=
  forallbz2 (λ y x, negb (L g y x))
  (seqz 0 (H g))
  (seqz 0 (W g)).

Definition FixPiece (pNew : Piece) (s : State) : option State :=
  option_map
    (λ s1' : T1.State,
      let clearedLines := clearedLines s1' in
      let combo' := (if clearedLines =? 0 then 0 else combo s + 1) in
      let perfectClear' := EmptyGridb (mg s1') in
      let totalClearedLines' := totalClearedLines s + clearedLines in
      {| s1 := s1'
      ;  combo := combo'
      ;  perfectClear := perfectClear'
      ;  (* req-score *) (* combo'-1 is 0 at min because of nat subtraction *)
         score := score s + (Points clearedLines (level s) (combo'-1) perfectClear')
      ;  totalClearedLines := totalClearedLines'
      ;  (* req-level-formula *) (* / is nat division *)
         level := 1 + totalClearedLines' / 10
      |}
    )
    (T1.FixPiece pNew (s1 s)).

Definition FallStep (pNew : T1.Piece) (s : State) : option State :=
  match MovePiece (-1, 0)%Z s with
  | Some s' => Some s'
  | None    => FixPiece pNew s
  end.

Definition Next (e : Event) (s : State) : option State :=
  match e with
  | Move dyx  => MovePiece dyx s
  | Rotate cw => RotatePiece cw s
  | Fix pNew  => FixPiece pNew s
  | Fall pNew => FallStep pNew s
  | Stutter   => Some s
  end.


(* ========================================================================= *)
(* State invariants                                                          *)
(* ========================================================================= *)

Definition LevelCorrect (s : State) : Prop :=
  level s = 1 + (totalClearedLines s) / 10.

(* There's no point restating T1.Correct's conjuncts at the T2 level, because T2
states embed T1 states. *)
Definition Correct (s : State) : Prop :=
    T1.Correct (s1 s)
  ∧ LevelCorrect s.


(* ========================================================================= *)
(* Step invariants                                                           *)
(* ========================================================================= *)

Definition NonDecreasingScore (s s' : State) : Prop := ∀ e
  (Hn : Next e s = Some s'),
  score s <= score s'.

Definition NonDecreasingLevel (s s' : State) : Prop := ∀ e
  (Hn : Next e s = Some s'),
  level s <= level s'.

Definition ScoreRisesOnClear (s s' : State) : Prop := ∀ pNew
  (Hc : Correct s)
  (Hn : FixPiece pNew s = Some s')
  (Hl : 0 < clearedLines (s1 s')),
  score s < score s'.

Definition CorrectStep (s s' : State) : Prop :=
    NonDecreasingScore s s'
  ∧ NonDecreasingLevel s s'
  ∧ ScoreRisesOnClear s s'.


(* ========================================================================= *)
(* Refinement                                                                *)
(* ========================================================================= *)

(* Define the refinement mapping f with its event component and its state
component. *)

(* Event component: "identity" function *)
Definition fₑ (e2 : T2.Event) : T1.Event :=
  match e2 with
  | T2.Move dyx  => T1.Move dyx
  | T2.Rotate cw => T1.Rotate cw
  | T2.Fix pNew  => T1.Fix pNew
  | T2.Fall pNew => T1.Fall pNew
  | T2.Stutter   => T1.Stutter
  end.

(* State component: projection to T1.State *)
Definition fₛ : T2.State → T1.State :=
  s1.

(*
For T1 refinement to hold, this diagram must commute:
         e1
   s1    →    s1'
fₛ ↑     ⇑fₑ  ↑ fₛ
   s2    →    s2'
         e2
*)

Definition T2RefinesT1 : Prop :=
    (∀ p, fₛ (T2.Init p) = T1.Init p)
  ∧ (∀ s2 s2' e2
     (H1 : T2.Next e2 s2 = Some s2'),
     T1.Next (fₑ e2) (fₛ s2) = Some (fₛ s2')).

(* Now, the other direction: from T1 to T2.  *)

(* State reached from state s1 through events es1, if any. *)
Fixpoint RunT1 (es1 : list T1.Event) (s1 : T1.State) : option T1.State :=
  match es1 with
  | [] => Some s1
  | e1 :: es1' =>
      match T1.Next e1 s1 with
      | Some s1' => RunT1 es1' s1'
      | None => None
      end
  end.

(* (fₑ, gₑ) forms an isomorphism. *)
Definition gₑ (e1 : T1.Event) : T2.Event :=
  match e1 with
  | T1.Move dyx  => T2.Move dyx
  | T1.Rotate cw => T2.Rotate cw
  | T1.Fix pNew  => T2.Fix pNew
  | T1.Fall pNew => T2.Fall pNew
  | T1.Stutter   => T2.Stutter
  end.

(* State reached from state s2 through events es2, if any. *)
Fixpoint RunT2 (es2 : list T2.Event) (s2 : T2.State) : option T2.State :=
  match es2 with
  | [] => Some s2
  | e2 :: es2' =>
      match T2.Next e2 s2 with
      | Some s2' => RunT2 es2' s2'
      | None => None
      end
  end.

(* T2 allows all behaviors T1 does: fₛ is surjective on reachable states and has
a deterministic section that adds the new T2 fields. This corresponds to the
following commuting diagram where esX is a list of TX.Event (X ∈ {1, 2}):

               es1
   T1.Init p   →         s1'
fₛ ↑           ⇓ map gₑ  ↑ fₛ
   T2.Init p   →         s2'
               es2
*)
Definition T2AllowsAllT1 : Prop := ∀ p es1 s1'
  (H1 : RunT1 es1 (T1.Init p) = Some s1'), (* s1' is reachable via events es1 *)
  ∃ s2',
      (* s2' is reachable via events (map gₑ es1) *)
      RunT2 (map gₑ es1) (T2.Init p) = Some s2'
      (* fₛ admits a deterministic section along reachable traces *)
    ∧ fₛ s2' = s1'.


(* ========================================================================= *)
(* Helpers for refining models                                               *)
(* ========================================================================= *)

Definition UnchangedT2Part (s : State) (s1 : T1.State) : State :=
  {| s1 := s1
  ;  score := score s
  ;  level := level s
  ;  combo := combo s
  ;  perfectClear := perfectClear s
  ;  totalClearedLines := totalClearedLines s
  |}.

Definition CorrectWithoutGameover (s : State) : Prop :=
    T1.CorrectWithoutGameover (s1 s)
  ∧ LevelCorrect s.

Definition mg (s : State) : Grid :=
  T1.mg (s1 s).

Definition gameover (s : State) : bool :=
  T1.gameover (s1 s).
