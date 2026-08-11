
(***************************************************************************
This model extends T3 with the next pieces preview mechanics.


# New addressed requirements

req-preview-len, req-preview-init, req-preview-pop

(see definitions_requirements.md)


# Design

New pieces are picked from a "bag", which is simply a set of pieces. Initially,
the bag contains all pieces. When it becomes empty (on FixPiece or HoldPiece) it
is replaced by another bag that is provided as input to the corresponding
events. This follows the same approach as the new piece in
T1.{FixPiece,FallStep}. Corresponding events therefore take new parameters.


# Parameters

The model is parameterized by the piece preview length (`NextLen`) and the bag
length (`MaxBagLen`).


# Invariants

State invariants ensure the consistency of the bag with the preview. Step
invariants are unchanged from T3.


# Refinement

This model is a restriction on T4. The bag/preview mechanism ensures picking the
new piece is "fair" in some sense, thus excluding behaviors where it is "unfair"
(e.g. same new piece X times in a row). Outside this restriction, all T3
mechanisms are kept unchanged, so T4 obviously refines T3 (but not the other way
around).

Note that contrary to previous refinements, the T4 to T3 event mapping requires
the current T4 state to determine the next piece and put it in the T3 event.

 ***************************************************************************)

From Tetris Require T3.
Import T1(Piece).
From Tetris Require Import Notations.

Open Scope nat_scope.

Parameter NextLen : ℕ. (* req-preview-len: preview length is constant *)
Parameter MaxBagLen : ℕ.

Axiom AxiomsMaxBagLen : MaxBagLen > 0.


(* ========================================================================= *)
(* Specification                                                             *)
(* ========================================================================= *)

(* bag_ and next_ are sequences of pieces. They are modeled as
   unbounded function + bound, similar to Grid in T1, for
   simple typing and easy access (function application).
   bag_ is bounded by bagLen_ and next_ is bounded by NextLen.
   Trailing underscore is to reserve plain name (bag, bagLen, next) for
   projection on State (see below). *)
Record Draw := mkDraw
  { bag_    : ℕ → Piece (* source to complete next_; pieces are drawn backwards *)
  ; bagLen_ : ℕ         (* bound for bag_ *)
  ; next_   : ℕ → Piece (* next_ 0 is the next piece *)
  }.

Record State := mkState
  { s3 : T3.State
  ; d  : Draw
  }.

Definition bag (s : State) : ℕ → Piece := bag_ (d s).
Definition bagLen (s : State) : ℕ := bagLen_ (d s).
Definition next (s : State) : ℕ → Piece := next_ (d s).
Definition gameover (s : State) : bool := T3.gameover (s3 s).
Definition hold (s : State) : option Piece := T3.hold (s3 s).
Definition score (s : State) : ℕ := T3.score (s3 s).
Definition level (s : State) : ℕ := T3.level (s3 s).
Definition clearedLines (s : State) : ℕ := T3.clearedLines (s3 s).

(* f is bijective on range [0, len). *)
Definition Bijective [A : Type] (f : ℕ → A) (len : ℕ) : Prop :=
    (∀ i j : ℕ, i < len → j < len → f i = f j → i = j) (* injective *)
  ∧ (∀ a : A, ∃ i, i < len ∧ f i = a). (* surjective *)

(* {bag i | 0 ≤ i < MaxBagLen} is in bijection with the set of pieces. *)
Definition PieceSet (bag : ℕ → Piece) : Prop :=
  Bijective bag MaxBagLen.

Definition TypeOK (s : State) : Prop :=
  PieceSet (bag s).

(* Example:
NextLen = 5
f       = [T, S, L, T, L]
pNew    = S
out     = [S, L, T, L, S]
*)
Definition ShiftNext (next : ℕ → Piece) (pNew : Piece) : ℕ → Piece :=
  λ i, if i =? NextLen - 1 then pNew else next (i + 1).

(*
Next piece (first of next) with updated Draw
(bag popped if len > 1 else bagNew,
next left-shifted with last = popped from bag).

Example:
d = {bag := [S L T]; next := [S L T L L S S]}
bagNew = [T L S]
out = (S, {bag := [S L]; next := [L T L L S S T]}
---
d = {bag := [S L]; next := [L T L L S S T]}
bagNew = [T L S]
out = (L, {bag := [S]; next := [T L L S S T L]})
---
d = {bag := [S]; next := [T L L S S T L]}
bagNew = [T L S]
out = (T, {bag := [T L S]; next := [L L S S T L S]})
---
d = {bag := [T L S]; next := [L L S S T L S]}
bagNew = [S T L]
out = (L, {bag := [T L]; next := [L S S T L S S]})
---
d = {bag := [T L]; next := [L S S T L S S]}
bagNew = [S T L]
out = (L, {bag := [T]; next := [S S T L S S L]})
---
d = {bag := [T]; next := [S S T L S S L]}
bagNew = [S T L]
out = (S, {bag := [S T L]; next := [S T L S S L T]})
---
d = {bag := [S T L]; next := [S T L S S L T]}
bagNew = [L S T]
out = (S, {bag := [S T]; next := [T L S S L T L]})
*)
(* req-preview-pop *)
Definition DrawNextPiece (d : Draw) (bagNew : ℕ → Piece) : Piece * Draw :=
  let bagSingle := bagLen_ d <=? 1 in
  (next_ d 0,
   {| bag_    := if bagSingle then bagNew else bag_ d
   ;  bagLen_ := if bagSingle then MaxBagLen else bagLen_ d - 1
   ;  next_   := ShiftNext (next_ d) (bag_ d (bagLen_ d - 1))
   |}).

(*
Draw pieces from bags to fill next.

Example:
d = { bag    := [S L T] (bagLen := 3 = MaxBagLen)
    ; next   := [S L T L L S S] (NextLen = 7) }
i = 7 (= NextLen)
bags = [[S L T] [T L S] [S T L] [L S T]...]
bagIdx = 1
---
d = {bag := [S L]; next := [L T L L S S T]}
i = 6
bags = [[S L T] [T L S] [S T L] [L S T]...]
bagIdx = 1
---
d = {bag := [S]; next := [T L L S S T L]}
i = 5
bags = [[S L T] [T L S] [S T L] [L S T]...]
bagIdx = 1
---
d = {bag := [T L S]; next := [L L S S T L S]}
i = 4
bags = [[S L T] [T L S] [S T L] [L S T]...]
bagIdx = 2
---
d = {bag := [T L]; next := [L S S T L S S]}
i = 3
bags = [[S L T] [T L S] [S T L] [L S T]...]
bagIdx = 2
---
d = {bag := [T]; next := [S S T L S S L]}
i = 2
bags = [[S L T] [T L S] [S T L] [L S T]...]
bagIdx = 2
---
d = {bag := [S T L]; next := [S T L S S L T]}
i = 1
bags = [[S L T] [T L S] [S T L] [L S T]...]
bagIdx = 3
---
d = {bag := [S T]; next := [T L S S L T L]}
i = 0
bags = [[S L T] [T L S] [S T L] [L S T]...]
bagIdx = 3
out = {bag := [S T]; next := [T L S S L T L]}
*)
Fixpoint BuildInitNext (d : Draw) (i : ℕ) (bags : ℕ → ℕ → Piece) (bagIdx : ℕ) : Draw * ℕ :=
  match i with
  | O => (d, bagIdx)
  | S i' =>
    let (_, d') := DrawNextPiece d (bags bagIdx) in
    let bagIdx' := bagIdx + (if bagLen_ d =? 1 then 1 else 0) in
    BuildInitNext d' i' bags bagIdx'
  end.

Definition InitPieceAndDraw (bags : ℕ → ℕ → Piece)
    (H : ∀ i, PieceSet (bags i)) : Piece * Draw :=
  (* In d, next_'s value is arbitrary since BuildInitNext will overwrite it. *)
  let d  := {| bag_ := bags 0; bagLen_ := MaxBagLen ; next_ := bags 0 |} in
  let (d', bagIdx) := BuildInitNext d NextLen bags 1 in (* req-preview-init *)
  DrawNextPiece d' (bags bagIdx).

Definition InitPiece
    (bags : ℕ → ℕ → Piece) (H : ∀ i, PieceSet (bags i)) : Piece :=
  fst (InitPieceAndDraw bags H).

(*
Example:
Piece     = {L, T, S}
NextLen   = 7
MaxBagLen = 3
bags      = [[S L T] [T L S] [S T L] [L S T]...]
*)
Definition Init (bags : ℕ → ℕ → Piece) (H : ∀ i, PieceSet (bags i)) : State :=
  let (p, d) := InitPieceAndDraw bags H in
  {| s3 := T3.Init p
  ;  d  := d
  |}.

Inductive Event :=
  | Move (dyx : ℤ × ℤ)
  | Rotate (cw : bool)
  | Fix (bagNew : ℕ → Piece) (H : PieceSet bagNew)
  | Fall (bagNew : ℕ → Piece) (H : PieceSet bagNew)
  | Hold (bagNew : ℕ → Piece) (H : PieceSet bagNew)
  | Stutter.

Definition UnchangedT4Part (s : State) (s3 : T3.State) : State :=
  {| s3 := s3
  ;  d  := d s (* unchanged *)
  |}.

(* Forward to T3. *)
Definition MovePiece (dyx : ℤ × ℤ) (s : State) : option State :=
  option_map (UnchangedT4Part s) (T3.MovePiece dyx (s3 s)).

(* Forward to T3. *)
Definition RotatePiece (clockwise : bool) (s : State) : option State :=
  option_map (UnchangedT4Part s) (T3.RotatePiece clockwise (s3 s)).

Definition FixPiece (bagNew : ℕ → Piece) (H : PieceSet bagNew) (s : State)
    : option State :=
  let (p, d') := DrawNextPiece (d s) bagNew in
  option_map (UnchangedT4Part (mkState (s3 s) d')) (T3.FixPiece p (s3 s)).

Definition FallStep (bagNew : ℕ → Piece) (H : PieceSet bagNew) (s : State)
    : option State :=
  match MovePiece (-1, 0)%Z s with
  | Some s' => Some s'
  | None    => FixPiece bagNew H s
  end.

Definition HoldPiece (bagNew : ℕ → Piece) (H : PieceSet bagNew) (s : State)
    : option State :=
  if ! (gameover s) then
    (* p is the new piece only if hold is empty (see T3.HoldPiece), otherwise it is
       unused.
       d'' is the updated Draw only if hold is empty. *)
    let (p, d') := DrawNextPiece (d s) bagNew in
    let d'' := match hold s with Some _ => d s | None => d' end in
    option_map (UnchangedT4Part (mkState (s3 s) d'')) (T3.HoldPiece p (s3 s))
  else
    None.

Definition Next (e : Event) (s : State) : option State :=
  match e with
  | Move dyx      => MovePiece dyx s
  | Rotate cw     => RotatePiece cw s
  | Fix bagNew H  => FixPiece bagNew H s
  | Fall bagNew H => FallStep bagNew H s
  | Hold bagNew H => HoldPiece bagNew H s
  | Stutter       => Some s
  end.


(* ========================================================================= *)
(* State invariants                                                          *)
(* ========================================================================= *)

(* The last next pieces are drawn from the bag.
Examples:
 Piece = {A, B, C}
 NextLen = 5
 MaxBagLen = 3
 bag = [A B C]
 bagLen = 1
 next = [C A C A B] -> [A C A B C] -> [C A B C B]
 k = min (3-1) 5 = 2
 i: 0 ↦ next (5-0-1) = bag (1+0) ≣ B = B
    1 ↦ next (5-1-1) = bag (1+1) ≣ C = C
---
 Piece = {A, B, C, D}
 NextLen = 2
 MaxBagLen = 4
 bag = [A B C D]
 bagLen = 1
 next = [B A] -> [A D] -> [D C] -> [C B]
 k = min (4-1) 2 = 2
 i: 0 ↦ next (2-0-1) = bag (1+0) ≣ B = B
    1 ↦ next (2-1-1) = bag (1+1) ≣ C = C
*)
Definition BagNextConsistentD (dd : Draw) : Prop :=
  let k := min (MaxBagLen - bagLen_ dd) NextLen in
  ∀ i : ℕ, i < k →
    next_ dd (NextLen - i - 1) = bag_ dd (bagLen_ dd + i).

Definition CorrectD (dd : Draw) : Prop :=
    PieceSet (bag_ dd) (* TypeOK *)
  ∧ 0 < bagLen_ dd    (* BagNonEmpty *)
  ∧ BagNextConsistentD dd.

Definition BagNonEmpty (s : State) : Prop :=
  0 < bagLen s.

Definition BagNextConsistent (s : State) : Prop :=
  BagNextConsistentD (d s).

Definition Correct (s : State) : Prop :=
    T3.Correct (s3 s)
  ∧ CorrectD (d s).


(* ========================================================================= *)
(* Step invariants                                                           *)
(* ========================================================================= *)

Definition CorrectStep (s s' : State) : Prop :=
    T3.CorrectStep (s3 s) (s3 s').


(* ========================================================================= *)
(* Refinement                                                                *)
(* ========================================================================= *)

(* The refinement holds since T4's changes affect either new state variables
   (Draw), or the new piece given to T3's events (FixPiece, HoldPiece). *)

Definition fₛ : T4.State → T3.State :=
  s3.

(* Contrary to previous models, the event mapping depends here on the state.
Consider a T4 step: s4 --(T4.Fix bagNew _)--> s4'
When a piece fixes, a new piece appears. In T3, this new piece is explicitly
given by the caller. In T4, it is fully determined by the current state, and is
popped from the next piece sequence. Then, this sequence and the bag of pieces are
updated. If the next piece is determined to be X, then the T4 step refines
`T3.FixPiece X (s3 s4)`.
*)
Definition fₑ (s : T4.State) (e : T4.Event) : T3.Event :=
  match e with
  | T4.Move dyx      => T3.Event2 (T2.Move dyx)
  | T4.Rotate cw     => T3.Event2 (T2.Rotate cw)
  | T4.Fix bagNew _  => T3.Event2 (T2.Fix (next s 0))
  | T4.Fall bagNew _ => T3.Event2 (T2.Fall (next s 0))
  | T4.Hold bagNew _ => T3.Hold (next s 0)
  | T4.Stutter       => T3.Event2 T2.Stutter
  end.

(*
For T3 refinement to hold, this diagram must commute:
         e3
   s3    →         s3'
fₛ ↑     ⇑(fₑ s4)  ↑ fₛ
   s4    →         s4'
         e4
*)

Definition T4RefinesT3 : Prop :=
    (∀ bags HSet, fₛ (T4.Init bags HSet) = T3.Init (T4.InitPiece bags HSet))
  ∧ (∀ e4 s4 s4'
    (H1 : T4.Next e4 s4 = Some s4'),
    T3.Next (fₑ s4 e4) (fₛ s4) = Some (s3 s4')).


(* ========================================================================= *)
(* Helpers for refining models                                               *)
(* ========================================================================= *)

Definition py (s : State) : ℤ := T1.py (T2.s1 (T3.s2 (s3 s))).
Definition px (s : State) : ℤ := T1.px (T2.s1 (T3.s2 (s3 s))).
Definition pr (s : State) : ℤ := T1.pr (T2.s1 (T3.s2 (s3 s))).
Definition p (s : State) : Piece := T3.p (s3 s).
Definition mg (s : State) : T1.Grid := T1.mg (T2.s1 (T3.s2 (s3 s))).
Definition perfectClear (s : State) : bool := T3.perfectClear (s3 s).

Definition CorrectWithoutGameover (s : State) : Prop :=
    T3.CorrectWithoutGameover (s3 s)
  ∧ CorrectD (d s).
