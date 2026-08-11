(***************************************************************************
This model extends T2 with the hold mechanics.

When the player holds the current piece, this piece is placed in the hold slot.
If the hold slot is not empty, the held piece is swapped with the current piece.
In both cases, the new current piece appears at its initial position and
rotation. Holding is only allowed once per piece: once current piece is held,
the player must fix the new current piece before being able to hold again.


# New addressed requirements

req-hold, req-hold-swap, req-hold-empty, req-hold-limit

(see definitions_requirements.md)


# Design

This model adds a new event: holding the current piece (see `Hold`). Among T2
events, only fixing the piece is orthogonally extended to re-enable holding;
others are unchanged.

Holding the piece is genuinely new and affects T1 by changing the current piece.
As for FixPiece, the new piece is a parameter of HoldPiece.


# Invariants

In addition to state invariants, this model defines a new step invariant:

- once the hold slot is set, it cannot be empty again (see `HoldMonotone`)


# Refinement

Because holding a piece is a genuinely new event, T3 does not refine T2: the T3
behaviors in which a piece is held cannot be mapped to T2 behaviors.

However, T3 minus holding a piece does obviously refine T2, as these T3 events
only touch orthogonal data.

It is also true that T3 allows all behaviors T2 does. See T2 for the approach.

 ***************************************************************************)

From Tetris Require T1 T2.
Import T1(Piece, Grid).
Import T2(s1).
From Tetris Require Import Notations.
From Stdlib Require Import List.
Import ListNotations.

Open Scope nat_scope.

(* No new parameter. *)

(* ========================================================================= *)
(* Specification                                                             *)
(* ========================================================================= *)

Record State := mkState
  { s2 : T2.State
  ; hold : option Piece (* the piece being held *)
  ; swapped : bool (* true iff the current piece comes from the hold box *)
  }.

Definition gameover (s : State) : bool := T1.gameover (s1 (s2 s)).
Definition p (s : State) : Piece := T1.p (s1 (s2 s)).
Definition score (s : State) : ℕ := T2.score (s2 s).
Definition level (s : State) : ℕ := T2.level (s2 s).
Definition clearedLines (s : State) : ℕ := T1.clearedLines (s1 (s2 s)).

Definition Init (p : Piece) : State :=
  {| s2 := T2.Init p
  ;  hold := None
  ;  swapped := false
  |}.

Inductive Event :=
  | Event2 (e2 : T2.Event)
  | Hold (pNew : Piece).

Definition UnchangedT3Part (s : State) (s2 : T2.State) : State :=
  {| s2 := s2
  ;  hold := hold s       (* unchanged *)
  ;  swapped := swapped s (* unchanged *)
  |}.

(* Forward to T2. *)
Definition MovePiece (dyx : ℤ × ℤ) (s : State) : option State :=
  option_map (UnchangedT3Part s) (T2.MovePiece dyx (s2 s)).

(* Forward to T2. *)
Definition RotatePiece (clockwise : bool) (s : State) : option State :=
  option_map (UnchangedT3Part s) (T2.RotatePiece clockwise (s2 s)).

(* Forward to T2 and reenable swapping. *)
Definition FixPiece (pNew : Piece) (s : State) : option State :=
  option_map (λ s2,
    {| s2 := s2
    ;  swapped := false (* req-hold-limit: holding is allowed again after fixing *)
    ;  hold := hold s   (* unchanged *)
    |})
    (T2.FixPiece pNew (s2 s)).

Definition FallStep (pNew : Piece) (s : State) : option State :=
  match MovePiece (-1, 0)%Z s with
  | Some s' => Some s'
  | None    => FixPiece pNew s
  end.

(* req-hold, req-hold-swap, req-hold-empty, req-hold-limit *)
Definition HoldPiece (pNew : Piece) (s : State) : option State :=
  if ! gameover s && ! swapped s then (* req-hold-limit: cannot hold twice in a row *)
    let s2_ := s2 s in
    let p2 := match hold s with
      | Some p => p  (* req-hold-swap: held piece becomes current *)
      | None => pNew (* req-hold-empty: new piece becomes current *)
      end in
    Some {| s2 := T2.UnchangedT2Part s2_ (T1.NewPieceState p2 (s1 s2_))
         ;  hold := Some (p s) (* req-hold: put current piece in hold slot *)
         ;  swapped := true (* req-hold-limit: block further holds *)
         |}
  else
    None.

(* Next without Hold *)
Definition NextT2Event (e : T2.Event) (s : State) : option State :=
  match e with
  | T2.Move dyx  => MovePiece dyx s
  | T2.Rotate cw => RotatePiece cw s
  | T2.Fix pNew  => FixPiece pNew s
  | T2.Fall pNew => FallStep pNew s
  | T2.Stutter   => Some s
  end.

Definition Next (e : Event) (s : State) : option State :=
  match e with
  | Event2 e2 => NextT2Event e2 s
  | Hold pNew => HoldPiece pNew s
  end.


(* ========================================================================= *)
(* State invariants                                                          *)
(* ========================================================================= *)

(* Once a piece is swapped, the hold box is non-empty. *)
Definition SwappedImplyHoldSome (s : State) : Prop :=
  ∀ (H1 : swapped s = true),
  hold s ≠ None.

(* Gameover can only occur at initialization or after fixing a piece. Swapping
is possible initially and fixing a piece also reenables it. *)
Definition GameoverImplyNotSwapped (s : State) : Prop :=
  ∀ (H1 : gameover s = true),
  swapped s = false.

Definition Correct (s : State) : Prop :=
    T2.Correct (s2 s)
  ∧ SwappedImplyHoldSome s
  ∧ GameoverImplyNotSwapped s.


(* ========================================================================= *)
(* Step invariants                                                           *)
(* ========================================================================= *)

Definition HoldMonotone (s s' : State) : Prop := ∀ e
  (H1 : hold s ≠ None)
  (H2 : Next e s = Some s'),
  hold s' ≠ None.

Definition CorrectStep (s s' : State) : Prop :=
    T2.CorrectStep (s2 s) (s2 s')
  ∧ HoldMonotone s s'.


(* ========================================================================= *)
(* Refinement                                                                *)
(* ========================================================================= *)

(* The refinement holds only when excluding Hold, i.e. it holds on T2 events. *)

(* Define the refinement mapping f with its event component and its
   state component. *)

(* Event component: identity function *)
Definition fₑ : T2.Event → T2.Event :=
  id.

(* State component: projection to T2.State *)
Definition fₛ: T3.State → T2.State :=
  s2.

(*
For T2 refinement to hold, this diagram must commute:
         e2
   s2    →    s2'
fₛ ↑     ⇑fₑ  ↑ fₛ
   s3    →    s3'
         e2
*)

Definition T3RefinesT2 : Prop :=
    (∀ p, fₛ (Init p) = T2.Init p)
  ∧ (∀ s3 s3' e2
     (Hn : Next (Event2 e2) s3 = Some s3'),
     T2.Next (fₑ e2) (fₛ s3) = Some (fₛ s3')).

(* Now, the other direction: from T2 to T3. *)

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

(* State reached from state s3 through events es2, if any. *)
Fixpoint RunT3 (es2 : list T2.Event) (s3 : T3.State) : option T3.State :=
  match es2 with
  | [] => Some s3
  | e2 :: es2' =>
      match T3.NextT2Event e2 s3 with
      | Some s3' => RunT3 es2' s3'
      | None => None
      end
  end.

(* T3 allows all behaviors T2 does: fₛ is surjective on reachable states and has
a deterministic section that adds the new T3 fields. This corresponds to the
following commuting diagram where esX is a list of TX.Event (X ∈ {2, 3}):

               es2
   T2.Init p   →      s2'
fₛ ↑           ⇓ id   ↑ fₛ
   T3.Init p   →      s3'
               es2
*)
Definition T3AllowsAllT2 : Prop := ∀ p es2 s2'
  (H1 : RunT2 es2 (T2.Init p) = Some s2'), (* s2' is reachable via events es2 *)
  ∃ s3',
      (* s3' is reachable via events es2 *)
      RunT3 es2 (T3.Init p) = Some s3'
      (* fₛ admits a deterministic section along reachable traces *)
    ∧ fₛ s3' = s2'.


(* ========================================================================= *)
(* Helpers for refining models                                               *)
(* ========================================================================= *)

Definition perfectClear (s : State) : bool := T2.perfectClear (s2 s).

Definition CorrectWithoutGameover (s : State) : Prop :=
    T2.CorrectWithoutGameover (s2 s)
  ∧ SwappedImplyHoldSome s
  ∧ GameoverImplyNotSwapped s.

Definition mg (s : State) : Grid :=
  T2.mg (s2 s).
