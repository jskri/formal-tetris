(***************************************************************************

This model addresses the core mechanisms of Tetris: piece move/rotation, line
clearing, gameover.


# Addressed requirements

req-flow, req-piece-ctrl, req-piece-loc, req-piece-free, req-piece-init,
req-piece-move-dir, req-piece-move-def, req-piece-rot, req-piece-fall,
req-piece-fix, req-piece-fix-gameover, req-piece-fix-new, req-grid-clear

(see definitions_requirements.md)


# Design

## Grid

The main choice is to model grids as (unbounded) ℤ → ℤ → bool functions, packed
with dimensions and origin. Functions allow for easy access to rows and columns
(resp. first and second index), easy quantification and update. However, only
blocks inside bounds have meaningful values.

Pieces are also modeled as grids, with their position given by the origin of the
grid. Piece grids are square to avoid offset on rotations. A piece grid can be
partially outside the main grid, but only wrt its empty blocks: all occupied
blocks must be inside the main grid.

A small grid algebra then allows us to define all operations: union (∪),
intersection (∩), inclusion (⊆), translation (⊕), empty grid (∅) and make full
(Full, makes all blocks occupied) (for unicode input, see the dedicated
section below). This algebra is akin to a lattice. Operations have nice
properties: associativity, commutativity, distributivity, neutral elements,
absorbing elements, etc. We only prove the properties we need (see T1Proofs.v),
but recognizing well-known algebraic structures is anyway a good sign that
operations are well designed. Here are some examples of how the algebra is
used:

- checking the piece grid pg does not overlap the grid mg:
  pg ∩ mg ⊆ ∅

- checking the grid g1's bounding box (bbox) is inside the grid g2's bbox:
  Full g1 ⊆ Full g2

- merging the grid piece pg at offset yx with the grid mg, and clamping the
  result:
  (mg ∪ (pg ⊕ yx)) ∩ Full mg

Note: Remember that a model is optimized for conceptual clarity and
non-ambiguity. An implementation could reuse the grid operations as-is, or fuse
them for the sake of efficiency.

## Labeled transition system (LTS)

Following TLA+, the model is an LTS: a kind of state machine that may have
infinite states and transitions. Essentially, it is defined by a set of initial
states (the base case), and a "next" relation (the inductive case). A state may
have an arbitrary number of successors.

Here, the state is mainly composed of the main grid, the current piece with its
position and rotation, and a flag to know if the game is over. There are as many
initial states as there are pieces (see `Init`). The "next" relation is given by
`Next`, which is parameterized by an `Event` value for convenience. Events are:
moving the piece, rotating the piece, fixing it when it cannot go down anymore,
and the periodic fall step.

Note that time is intentionally not part of the model and nothing in it
mandates that the fall is really periodic. It is the responsibility of the
"controller" of this model to determine the fall pace. More generally, any
indirect source of non-determinism is excluded from the model. For instance,
while in an implementation the choice of the next piece typically implies some
randomness, the model explicitly takes the next piece as an argument in the
concerned events (see `Init`, `FixPiece` and `FallStep`).

Conceptually, `Next` is the union of the next relations of each event. The
relation of an event is defined by a step-function, from a state to an
*optional* next state. This is because the event may not trigger from a
particular state. The skeleton of an event step-function is always the same:
"IF the guard holds for the input state THEN some updated state ELSE none".

Also note that an event-step is atomic: it is either completed entirely or not
at all.


# Parameters

The model is quite general in that it does not fix:

- the exact piece set
- the grid dimensions
- the forbidden zone dimensions and position

However, some constraints (aka axioms) are needed for reasoning. For instance,
the dimensions of the grids cannot be null, the piece grids cannot be empty, or
the forbidden zone's bbox must be inside the main grid's bbox.


# Invariants

We are talking here of state invariants, i.e. properties that must be true for
all reachable states. They define what it means for a behavior (a sequence of
states obtained inductively from `Init` and `Next`) to be correct. The master
invariant is `Correct` and is a conjunction of sub-invariants. Some examples of
sub-invariants are:

- the game is over when the main grid intersects the forbidden grid (see
`Gameover`)

- pieces do not intersect with the occupied blocks of the main grid (see
  `PieceOnFreeBlocks`)

- the main grid has no full line (because full lines' clearing is part of
`FixPiece`, see `NoFullLine`)


# Proofs

The emphasis is here more on safety than on liveness. The main safety invariant
that is proved is `Correct`: initial states are correct, and if a state is
correct and an event-step is completed, the new state is also correct. See
`SpecCorrect` in `T1Proofs.v`.

A liveness property is also proved: the fact that as long as the game is not
over, fall-steps are possible (see `FallStepAlwaysSucceeds` in `T1Proofs.v`).
This, coupled with weak fairness on `FallStep` (meaning if `FallStep` is always
possible it will eventually occur; which is what will happen in any reasonable
implementation) ensures the system makes progress.


# Unicode

The model uses some unicode symbols for clarity. It reuses standard symbols when
possible and avoids inventing new notations. Here is some advice to input them.

## VSCode

The "Unicode Latex" extension can be used. Bind its "Unicode: Insert Math
Symbol" command, then use the latex name of the character. See below for the
list of unicode characters and their latex names. Fuzzy search is supported, and
for instance ∀ can be input with "all" instead of "\forall", or ℕ with "bn"
instead of "\BbbN".

## Vim

The `abbreviate` command can be used.

## Latex names

Character        Latex name
---------------- ------------
→                \to
∀                \forall
∃                \exists
λ                \lambda
ℕ                \BbbN
ℤ                \BbbZ
×                \times
∧                \wedge
∨                \vee
¬                \neg
≤                \le
≥                \ge
≠                \neq
⊆                \subseteq
⊈                \nsubseteq
∪                \cup
∩                \cap
⊕                \oplus
∅                \emptyset

***************************************************************************)

From Tetris Require Import Notations Quantifiers.

Record Grid := mkGrid
  { L  : ℤ → ℤ → bool (* lines *)
  ; HW : ℤ × ℤ        (* (height, width) *)
  ; YX : ℤ × ℤ        (* (y, x) origin *)
  }.

Definition H (g : Grid) : ℤ := fst (HW g).
Definition W (g : Grid) : ℤ := snd (HW g).
Definition Y (g : Grid) : ℤ := fst (YX g).
Definition X (g : Grid) : ℤ := snd (YX g).

Definition InBox (g : Grid) (y x : ℤ) : bool :=
  (Y g ≤? y <? Y g + H g) && (X g ≤? x <? X g + W g).

Definition OutsideBox (g : Grid) (y x : ℤ) : Prop :=
    y < Y g
  ∨ Y g + H g ≤ y
  ∨ x < X g
  ∨ X g + W g ≤ x.

Definition Contained (g : Grid) : Prop :=
  ∀ y x, OutsideBox g y x → L g y x = false.

(*
g1 = {|H:=4; W:=2; Y:=-1; X:=0|}
g2 = {|H:=3; W:=4; Y:=-2; X:=-1|}
minY = min -1 -2 = -2
minX = min 0 -1 = -1
topMax = max (-1+4) (-2+3) = 3
rightMax = max (0+2) (-1+4) = 3
out = {|H:=5; W:=4; Y:=-2; X:=-1|}

∪-associative: ∀ g1 g2 g3, (g1 ∪ g2) ∪ g3 = g1 ∪ (g2 ∪ g3)
∪-commutative: ∀ g1 g2, g1 ∪ g2 = g2 ∪ g1
∪-dependent-neutral: ∀ g, g ∪ Empty g = g
∪-dependent-absorbing: ∀ g, g ∪ Full g = Full g
*)
Definition GridUnion (g1 g2 : Grid) : Grid :=
  let minY := Z.min (Y g1) (Y g2) in
  let minX := Z.min (X g1) (X g2) in
  let topMax := Z.max (Y g1 + H g1) (Y g2 + H g2) in
  let rightMax := Z.max (X g1 + W g1) (X g2 + W g2) in
  {| L  := λ y x, L g1 y x || L g2 y x
  ;  HW := (topMax - minY, rightMax - minX)
  ;  YX := (minY, minX)
  |}.

(*
g1 = {|H:=4; W:=2; Y:=-1; X:=0|}
g2 = {|H:=3; W:=4; Y:=-3; X:=-1|}
maxY = max -1 -3 = -1
maxX = max 0 -1 = 0
topMin = min (-1+4) (-3+3) = 0
rightMin := min (0+2) (-1+4) = 2
out = {|H:=0-(-1)=1; W:=2-0=2; Y:=-1; X:=0|}

∩-associative: ∀ g1 g2 g3, (g1 ∩ g2) ∩ g3 = g1 ∩ (g2 ∩ g3)
∩-commutative: ∀ g1 g2, g1 ∩ g2 = g2 ∩ g1
Note: No neutral element because no max in ℤ, however:
∩-dependent-neutral: ∀ g, g ∩ Full g = g
∩-dependent-absorbing: ∀ g, g ∩ Empty g = Empty g
∩∪-distributive: ∀ g1 g2 g3, g1 ∩ (g2 ∪ g3) = (g1 ∩ g2) ∪ (g1 ∩ g3)
*)
Definition GridIntersect (g1 g2 : Grid) : Grid :=
  let maxY := Z.max (Y g1) (Y g2) in
  let maxX := Z.max (X g1) (X g2) in
  let topMin := Z.min (Y g1 + H g1) (Y g2 + H g2) in
  let rightMin := Z.min (X g1 + W g1) (X g2 + W g2) in
  {| L := λ y x, L g1 y x && L g2 y x
  ;  HW := (topMin - maxY, rightMin - maxX)
  ;  YX := (maxY, maxX)
  |}.

(*
⊕-group-action: (g ⊕ d1) ⊕ d2 = g ⊕ (d1 + d2)
⊕∪-distributive: (g1 ∪ g2) ⊕ d = (g1 ⊕ d) ∪ (g2 ⊕ d)
⊕∩-distributive: (g1 ∩ g2) ⊕ d = (g1 ⊕ d) ∩ (g2 ⊕ d)
*)
Definition GridTranslate (g : Grid) (d : ℤ × ℤ) : Grid :=
  let (dy, dx) := d in
  {| L  := λ y x, L g (y - dy) (x - dx)
  ;  HW := HW g
  ;  YX := (Y g + dy, X g + dx)
  |}.

Definition Constant (g : Grid) (b : bool) : Grid :=
  {| L  := λ _ _, b
  ;  HW := HW g
  ;  YX := YX g
  |}.

Definition Empty (g : Grid) : Grid :=
  Constant g false.

Definition Full (g : Grid) : Grid :=
  Constant g true.

(*
true iff all occupied blocks of grid g1 are also occupied in grid g2.
⊆-transitive: ∀ g1 g2 g3, g1 ⊆ g2 → g2 ⊆ g3 → g1 ⊆ g3.
⊆-law1: ∀ g1 g2 g3, g1 ⊆ (g2 ∩ g3) → g1 ⊆ g2 ∧ g1 ⊆ g3.
*)
Definition GridInclude (g1 g2 : Grid) : bool :=
  forallbz2 (λ y x,
    implb
      (L g1 y x)
      ((Y g2 ≤? y <? Y g2 + H g2) && (X g2 ≤? x <? X g2 + W g2) && (L g2 y x))
  )
  (seqz (Y g1) (H g1))
  (seqz (X g1) (W g1)).

Definition EmptyGrid : Grid :=
  {| L  := λ _ _, false
  ;  HW := (0, 0)
  ;  YX := (0, 0)
  |}.

(* Algebraic structure:
For a fixed box B, the set of grids with that exact box is in bijection with
Bool^(B ∩ ℤ×ℤ) — one Boolean per cell — via L. Under that bijection ∪, ∩ correspond
exactly to pointwise ||, &&. The lattice of grids-with-box-B is isomorphic to
the pointwise Boolean lattice Bool^(cells of B), which is the complete atomic
distributive lattice on those cells (each cell is an independent atom/coatom pair,
Empty/Full are literal bottom/top, and the lattice is Boolean, i.e. every element
has a complement — stronger than merely distributive)
*)

(* Operators ordered from weaker binding to stronger binding. *)
Notation "g1 ⊆ g2" := (GridInclude g1 g2) (at level 64, no associativity). (* \subseteq = ⊆ *)
Notation "g1 ⊈ g2" := (negb (GridInclude g1 g2)) (at level 64, no associativity). (* \nsubseteq = ⊈ *)
Notation "g1 ∪ g2" := (GridUnion g1 g2) (at level 63, left associativity). (* \cup = ∪ *)
Notation "g1 ∩ g2" := (GridIntersect g1 g2) (at level 62, left associativity). (* \cap = ∩ *)
Notation "g ⊕ d" := (GridTranslate g d) (at level 61, left associativity). (* \oplus = ⊕ *)
Notation "∅" := EmptyGrid. (* \emptyset = ∅ *)


(* ========================================================================= *)
(* Parameters & axioms                                                       *)
(* ========================================================================= *)

(* parameters of the model *)
Parameter Piece : Type. (* the set of pieces *)
Parameter InitialMainGrid ForbiddenGrid : Grid.
Parameter RotGrid : Piece → ℤ → Grid. (* grid of a rotated piece (by ccw quarters) *)
Parameter InitialYX : Piece → ℤ × ℤ. (* initial y, x of a piece *)
Parameter PW : ℤ. (* width of the pieces (=height of the pieces, since square grid) *)

Definition InitialY (p : Piece) : ℤ := fst (InitialYX p).
Definition InitialX (p : Piece) : ℤ := snd (InitialYX p).

(* Note on Contained (below): it is not used by the Correct proof. Since
 * FixPiece clamps the union with `∩ Full (mg s)`, occupied blocks spuriously
 * declared outside a grid's box can never leave the main grid's box, and no
 * invariant inspects content outside a box. Contained is needed for fidelity
 * (FullLineCount counting what it claims to count) and for the refinement of
 * this model by an implementation, not for safety. *)

Axiom AxiomsInitialYX :
  ∀ p : Piece,
      1 - PW ≤ InitialY p < H InitialMainGrid
    ∧ 1 - PW ≤ InitialX p < W InitialMainGrid.

Axiom AxiomsRotGrid :
  ∀ p : Piece,
      (∀ r : ℤ,
        0 ≤ r < 4 →
        let gr := RotGrid p r in
          HW gr = (PW, PW)
        ∧ YX gr = (0, 0)
        ∧ Contained gr
          (* no piece grid is empty *)
        ∧ (∃ y x : ℤ,
              (0 ≤ y < PW)
            ∧ (0 ≤ x < PW)
            ∧ L gr y x = true))
      (* pieces appear in the occupied part of the forbidden zone *)
    ∧ (RotGrid p 0 ⊕ InitialYX p) ⊆ ForbiddenGrid = true.

Axiom AxiomsPW :
  PW > 0.

Definition IsFullLine (g : Grid) (y : ℤ) : Prop :=
  ∀ x : ℤ, (X g ≤ x < X g + W g) → L g y x = true.

Axiom AxiomsInitialMainGrid :
    H InitialMainGrid > 0
  ∧ W InitialMainGrid > 0
  ∧ YX InitialMainGrid = (0, 0)
  ∧ Contained InitialMainGrid
    (* initial main grid has no full line (see NoFullLine invariant) *)
  ∧ ∀ y : ℤ, (0 ≤ y < H InitialMainGrid) → ¬ IsFullLine InitialMainGrid y.

Axiom AxiomsForbiddenGrid :
    H ForbiddenGrid > 0
  ∧ W ForbiddenGrid > 0
  ∧ Contained ForbiddenGrid
  ∧ Full ForbiddenGrid ⊆ Full InitialMainGrid = true.


(* ========================================================================= *)
(* Specification                                                             *)
(* ========================================================================= *)

Record State := mkState
  { mg : Grid        (* main grid *)
  ; p : Piece        (* current piece *)
  ; pyx : ℤ × ℤ      (* (y, x) of the current piece *)
  ; pr : ℤ           (* rotation of the current piece *)
  ; gameover : bool  (* true iff game is over *)
  ; clearedLines : ℕ (* number of lines clear in the last step *)
  }.

Definition py (s : State) : ℤ := fst (pyx s).
Definition px (s : State) : ℤ := snd (pyx s).

Definition TypeOK (s : State) : Prop :=
    HW (mg s) = HW InitialMainGrid
  ∧ YX (mg s) = YX InitialMainGrid
  ∧ 0 ≤ pr s ≤ 3.

Definition Init (p : Piece) : State :=
  {| mg := InitialMainGrid
  ;  p  := p
  ;  pyx := InitialYX p (* req-piece-init *)
  ;  pr := 0 (* no rotation *)
     (* It is the responsibility of the user to set InitialMainGrid
      * so that the game isn't instantly over. *)
  ;  gameover := (ForbiddenGrid ∩ InitialMainGrid) ⊈ ∅
  ;  clearedLines := 0
  |}.

(* Events, parametrized where non-determinism exists.                      *)
(*   Move dyx  : translate piece by dyx=(dy, dx)                           *)
(*   Rotate cw : rotate clockwise (cw=true) or counter-clockwise           *)
(*   Fix pNew  : fix current piece; pNew is the next piece chosen          *)
(*   Fall pNew : periodic fall: move down if possible, else Fix            *)
(*   Stutter   : no-op (models stuttering steps)                           *)
Inductive Event :=
  | Move    (dyx  : ℤ × ℤ)
  | Rotate  (cw   : bool)
  | Fix     (pNew : Piece)
  | Fall    (pNew : Piece)
  | Stutter.

(* true iff piece p_ at pos (py_, px_) and rotated by angle pr_ is inside
 * main grid bounds and doesn't intersect it *)
Definition Valid (g : Grid) (p : Piece) (pyx : ℤ × ℤ) (pr : ℤ) : bool :=
  let gp := RotGrid p pr ⊕ pyx in
  (gp ⊆ Full g) && (gp ∩ g ⊆ ∅).

Definition CanMovePiece (dyx : ℤ × ℤ) (s : State) : bool :=
  let (dy, dx) := dyx in
  let pyx2 := (py s + dy, px s + dx) in (* req-piece-move-def *)
  ((dy =?  0) && (dx =? -1) ||
   (dy =?  0) && (dx =?  1) ||
   (dy =? -1) && (dx =?  0)) &&
  Valid (mg s) (p s) pyx2 (pr s). (* req-piece-move-dir *)

(* move the current piece by offset (dy, dx), if valid *)
Definition MovePiece (dyx : ℤ × ℤ) (s : State) : option State :=
  let (dy, dx) := dyx in
  let pyx2 := (py s + dy, px s + dx) in (* req-piece-move-def *)
  if ! gameover s && CanMovePiece dyx s then (* req-piece-move-dir *)
    Some {| pyx := pyx2
         ;  mg := mg s; p := p s; pr := pr s; gameover := gameover s
         ;  clearedLines := clearedLines s (* unchanged *)
         |}
  else
    None.

Definition RotatePiece (clockwise : bool) (s : State) : option State :=
  let pr2 := (pr s + (if clockwise then -1 else 1)) mod 4 in
  if ! gameover s && Valid (mg s) (p s) (pyx s) pr2 then
    Some {| pr := pr2
         ;  mg := mg s; p := p s; pyx := pyx s; gameover := gameover s
         ;  clearedLines := clearedLines s (* unchanged *)
         |}
  else
    None.

Definition Resize (g : Grid) (newGh : ℤ) (fillValue : ℤ → bool) : Grid :=
  {| L  := λ y, if y <? (Y g + H g) then L g y else fillValue
  ;  HW := (newGh, W g)
  ;  YX := YX g
  |}.

Definition IsFullLineb (g : Grid) (y : ℤ) : bool :=
  implb (Y g ≤? y <? Y g + H g) (forallbz (L g y) (seqz (X g) (W g))).

Fixpoint FilterFullLines (g : Grid) (fuel : ℕ) (y i : ℤ) : Grid :=
  match fuel with
  | O => {| L := λ _ _, false; HW := (0, W g); YX := YX g |}
  | S fuel =>
    if IsFullLineb g y then
      FilterFullLines g fuel (y+1) i
    else
      let g2 := FilterFullLines g fuel (y+1) (i+1) in
      {| L  := λ y1, if y1 =? i then L g y else L g2 y1
      ;  HW := (1 + H g2, W g)
      ;  YX := YX g
      |}
  end.

(* Grid g with full lines "cut" and non-full line above shifted down. Filled
 * with empty lines on top if necessary. *)
Definition ClearFullLines (g : Grid) : Grid :=
  let g2 := FilterFullLines g (Z.to_nat (H g)) (Y g) (Y g) in
  Resize g2 (H g) (λ _, false).

Section Nat.
  Open Scope nat_scope.

  Fixpoint FullLineCountImpl (g : Grid) (fuel : ℕ) (y : ℤ) : ℕ :=
    match fuel with
    | O => 0
    | S fuel' =>
      let count :=
        if IsFullLineb g (y + Z.of_nat fuel') then 1 else 0 in
      count + (FullLineCountImpl g fuel' y)
    end.
End Nat.

Definition FullLineCount (g : Grid) : ℕ :=
  FullLineCountImpl g (Z.to_nat (H g)) (Y g).

Definition PieceGrid (s : State) : Grid :=
  RotGrid (p s) (pr s).

Definition FixPiece (pNew : Piece) (s : State) : option State :=
  if ! gameover s && ! CanMovePiece (-1, 0) s then
    let u := (mg s ∪ (PieceGrid s ⊕ pyx s)) ∩ Full (mg s) in
    let mg2 := ClearFullLines u in (* req-grid-clear *)
    Some {| mg := mg2
         ;  p := pNew
         ;  pyx := InitialYX pNew
         ;  pr := 0
         ;  gameover := ForbiddenGrid ∩ mg2 ⊈ ∅ (* req-piece-fix-gameover *)
         ;  clearedLines := FullLineCount u
         |}
  else
    None.

(* Fall: periodic fall step — move down if possible, else fix.
   Never fails when not gameover. *)
Definition FallStep (pNew : Piece) (s : State) : option State :=
  match MovePiece (-1, 0) s with
  | Some s' => Some s'          (* req-piece-fall *)
  | None    => FixPiece pNew s (* req-piece-fix *)
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
(* Invariants                                                                *)
(* ========================================================================= *)

(* inv-gameover: game is over iff the main grid intersects the forbidden zone.*)
Definition Gameover (s : State) : Prop :=
  gameover s = true ↔ (ForbiddenGrid ∩ mg s) ⊈ ∅ = true.

Definition PieceOccupiedInsideBounds (s : State) : Prop :=
  (PieceGrid s ⊕ pyx s) ⊆ Full (mg s) = true.

Definition PieceOnFreeBlocks (s : State) : Prop := (* req-piece-free *)
  gameover s = false →
    (PieceGrid s ⊕ pyx s) ∩ (mg s) ⊆ ∅ = true.

Definition HasFullLine (g : Grid) : Prop :=
  ∃ y : ℤ, (Y g ≤ y < Y g + H g) ∧ IsFullLine g y.

Definition NoFullLine (s : State) : Prop :=
  ¬ HasFullLine (mg s).

(* useful for refining models *)
Definition CorrectWithoutGameover (s : State) : Prop :=
    TypeOK s
  ∧ PieceOccupiedInsideBounds s
  ∧ PieceOnFreeBlocks s
  ∧ NoFullLine s.

(* Master invariant. *)
Definition Correct (s : State) : Prop :=
    CorrectWithoutGameover s
  ∧ Gameover s.


(* ========================================================================= *)
(* Helpers for refining models                                               *)
(* ========================================================================= *)

Definition NewPieceState (pNew : Piece) (s : State) : State :=
  {| p := pNew
  ;  pyx := InitialYX pNew
  ;  pr := 0
     (* rest is unchanged *)
  ;  mg := mg s; gameover := gameover s; clearedLines := clearedLines s
  |}.

Definition NewPieceYXState (pyxNew : ℤ × ℤ) (s : State) : State :=
  {| pyx := pyxNew
     (* rest is unchanged *)
  ;  mg := mg s; p := p s; pr := pr s; gameover := gameover s;
     clearedLines := clearedLines s
  |}.

Definition NewMainGridGameoverState (mg : Grid) (gameover : bool) (s : State) : State :=
  {| mg := mg
  ;  gameover := gameover
     (* rest is unchanged *)
  ;  pyx := pyx s; p := p s; pr := pr s; clearedLines := clearedLines s
  |}.
