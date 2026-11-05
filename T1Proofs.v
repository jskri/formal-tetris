From Stdlib Require Import Lia Bool.
From Tetris Require Import T1 Notations Quantifiers QuantifiersProofs.

(* ========================================================================= *)
(* Reflection: from the boolean quantifiers to logical ones                  *)
(* ========================================================================= *)

(* This is the only section where [forallbz2], and hence [seqz], is unfolded.
 * Everything below it speaks of boxes and occupied blocks. *)

Lemma InRangeTrue : ∀ a b c : ℤ, (a ≤? b <? c) = true ↔ a ≤ b < c.
Proof.
  intros; rewrite andb_true_iff, Z.leb_le, Z.ltb_lt; tauto.
Qed.

Lemma InBoxTrue : ∀ (g : Grid) (y x : ℤ),
  InBox g y x = true ↔ (Y g ≤ y < Y g + H g) ∧ (X g ≤ x < X g + W g).
Proof.
  intros; unfold InBox; rewrite andb_true_iff, !InRangeTrue; tauto.
Qed.

(* The empty grid has an empty box, hence no block at all. *)
Lemma InBoxEmpty : ∀ y x : ℤ, InBox ∅ y x = false.
Proof.
  intros; apply not_true_iff_false; rewrite InBoxTrue; cbn; lia.
Qed.

(* Every occupied block of g1's box is a block of g2's box, and
 * is occupied there. Note the box membership of g2 in the conclusion: it is
 * what makes ⊆ transitive. *)
Lemma GridIncludeSpec : ∀ g1 g2 : Grid,
  g1 ⊆ g2 = true ↔
  (∀ (y x : ℤ) (Hb1 : InBox g1 y x = true) (Hl1 : L g1 y x = true),
     InBox g2 y x = true ∧ L g2 y x = true).
Proof.
  intros; unfold GridInclude; rewrite forallbz2Forall; split.
  - intros Hall; intros.
    (* Hall, at block (y, x) of g1's box, is an implication from L g1 y x. *)
    assert (Himp : implb (L g1 y x) (InBox g2 y x && L g2 y x) = true)
      by (apply Hall; apply InBoxTrue in Hb1; lia).
    rewrite Hl1 in Himp; cbn [implb] in Himp.
    apply andb_true_iff in Himp; tauto.
  - (* Hy and Hx, the ranges of y and x, are only used by lia. *)
    intros Hall y x Hy Hx.
    destruct (L g1 y x) eqn: Hl1; [ cbn [implb] | reflexivity ].
    apply andb_true_iff, Hall; (assumption || (apply InBoxTrue; lia)).
Qed.

Lemma GridIncludeIntro : ∀ g1 g2 : Grid,
  (∀ (y x : ℤ) (Hb1 : InBox g1 y x = true) (Hl1 : L g1 y x = true),
     InBox g2 y x = true ∧ L g2 y x = true) →
  g1 ⊆ g2 = true.
Proof.
  intros; apply GridIncludeSpec; assumption.
Qed.

Lemma GridIncludeElim : ∀ g1 g2 : Grid,
  g1 ⊆ g2 = true →
  ∀ (y x : ℤ) (Hb1 : InBox g1 y x = true) (Hl1 : L g1 y x = true),
    InBox g2 y x = true ∧ L g2 y x = true.
Proof.
  intros g1 g2; apply GridIncludeSpec.
Qed.

Lemma IsFullLinebFalseElim : ∀ (g : Grid) (y : ℤ)
  (HF : IsFullLineb g y = false),
  ¬ IsFullLine g y.
Proof.
  intros; intros HFull; unfold IsFullLineb in HF.
  assert (E : forallbz (L g y) (seqz (X g) (W g)) = true)
    by (apply forallbzIntro; exact HFull).
  rewrite E, implb_true_r in HF; discriminate HF.
Qed.


(* ========================================================================= *)
(* Box algebra                                                               *)
(* ========================================================================= *)

(* [Full g] depends on g's box only, hence Full is box-extensional. *)
Lemma FullBoxEq : ∀ (g1 g2 : Grid)
  (EHW : HW g1 = HW g2)
  (EYX : YX g1 = YX g2),
  Full g1 = Full g2.
Proof.
  intros; unfold Full, Constant; rewrite EHW, EYX; reflexivity.
Qed.

(* The box of an intersection is the intersection of the boxes. This is what
 * makes ∩ the meet of ⊆, unconditionally. *)
Lemma InBoxIntersectTrue : ∀ (g1 g2 : Grid) (y x : ℤ),
  InBox (g1 ∩ g2) y x = true ↔ InBox g1 y x = true ∧ InBox g2 y x = true.
Proof.
  intros; rewrite !InBoxTrue; unfold GridIntersect, Y, X, H, W; cbn; lia.
Qed.

Lemma GridIncludeTransitive : ∀ g1 g2 g3
  (H1 : g1 ⊆ g2 = true)
  (H2 : g2 ⊆ g3 = true),
  g1 ⊆ g3 = true.
Proof.
  intros; apply GridIncludeIntro; intros.
  (* H1 gives membership in g2's box, which is exactly what H2 needs. *)
  assert (Hb2 : InBox g2 y x = true)
    by (apply GridIncludeElim with (g1 := g1); assumption).
  assert (Hl2 : L g2 y x = true)
    by (apply GridIncludeElim with (g1 := g1); assumption).
  apply GridIncludeElim with (g1 := g2); assumption.
Qed.

(* [Full g1] has g1's box and is everywhere occupied. *)
Lemma GridIncludeFullImpliesNonFull : ∀ g1 g2
  (H1 : Full g1 ⊆ g2 = true),
  g1 ⊆ g2 = true.
Proof.
  intros; apply GridIncludeIntro; intros.
  apply GridIncludeElim with (g1 := Full g1); (assumption || reflexivity).
Qed.

Lemma GridIntersectMonotoneLeft : ∀ g1 g2 g3
  (H1 : g1 ⊆ g2 = true),
  g1 ∩ g3 ⊆ g2 ∩ g3 = true.
Proof.
  intros; apply GridIncludeIntro; intros.
  apply InBoxIntersectTrue in Hb1.
  cbn [L GridIntersect] in Hl1; apply andb_true_iff in Hl1.
  assert (Hb1g1 : InBox g1 y x = true) by tauto.
  assert (Hl1g1 : L g1 y x = true) by tauto.
  assert (Hb2 : InBox g2 y x = true)
    by (apply GridIncludeElim with (g1 := g1); assumption).
  assert (Hl2 : L g2 y x = true)
    by (apply GridIncludeElim with (g1 := g1); assumption).
  rewrite InBoxIntersectTrue; cbn [L GridIntersect]; rewrite andb_true_iff; tauto.
Qed.

(* Clamping a union back onto its left operand's box: the box arithmetic is
 * pure absorption, min (max a b) a = a and max (min a b) a = a. *)
Lemma BoxUnionClamp : ∀ g1 g2 : Grid,
    HW ((g1 ∪ g2) ∩ Full g1) = HW g1
  ∧ YX ((g1 ∪ g2) ∩ Full g1) = YX g1.
Proof.
  intros; unfold GridIntersect, GridUnion, Full, Constant, Y, X, H, W.
  split; apply injective_projections; cbn; lia.
Qed.


(* ========================================================================= *)
(* Line clearing                                                             *)
(* ========================================================================= *)

Lemma FilterFullLinesS : ∀ (g : Grid) (f : ℕ) (y i : ℤ),
  FilterFullLines g (S f) y i =
    if IsFullLineb g y then
      FilterFullLines g f (y + 1) i
    else
      {| L  := λ y1, if y1 =? i then L g y else L (FilterFullLines g f (y+1) (i+1)) y1
      ;  HW := (1 + H (FilterFullLines g f (y+1) (i+1)), W g)
      ;  YX := YX g
      |}.
Proof.
  reflexivity.
Qed.

(* Filtering changes the height only. *)
Lemma FilterFullLinesBox : ∀ (g : Grid) (fuel : ℕ) (y i : ℤ),
    W (FilterFullLines g fuel y i) = W g
  ∧ YX (FilterFullLines g fuel y i) = YX g.
Proof.
  induction fuel as [| f IH]; intros.
  - now split. (* fuel = 0 *)
  - rewrite FilterFullLinesS; destruct (IsFullLineb g y). (* fuel = S n *)
    + apply IH.
    + now split.
Qed.

(* At most one line per unit of fuel is kept. *)
Lemma FilterFullLinesHeight : ∀ (g : Grid) (fuel : ℕ) (y i : ℤ),
  0 ≤ H (FilterFullLines g fuel y i) ≤ Z.of_nat fuel.
Proof.
  induction fuel as [| f IH]; intros.
  - cbn; lia.
  - rewrite FilterFullLinesS; destruct (IsFullLineb g y).
    + specialize IH with (y := y + 1) (i := i); lia.
    + specialize IH with (y := y + 1) (i := i + 1); cbn [H HW fst]; lia.
Qed.

(* The lines of the filtered grid, at indices [i .. i + height), are exactly
 * non-full lines of g taken from [y .. y + fuel). Stated on [i] rather than on
 * [Y (result)]: in the recursive calls [i] runs ahead of [Y g], and the two
 * coincide only at the top-level call made by ClearFullLines. *)
Lemma FilterFullLinesRows : ∀ (g : Grid) (fuel : ℕ) (y i j : ℤ)
  (Hj : i ≤ j < i + H (FilterFullLines g fuel y i)),
  ∃ y' : ℤ,
      y ≤ y' < y + Z.of_nat fuel
    ∧ IsFullLineb g y' = false
    ∧ L (FilterFullLines g fuel y i) j = L g y'.
Proof.
  induction fuel as [| f IH]; intros.
  - (* No fuel: no line at all. *)
    cbn in Hj; lia.
  - rewrite FilterFullLinesS in *; destruct (IsFullLineb g y) eqn: EF.
    + (* Line y is full: dropped; the result is the recursive one. *)
      specialize IH with (y := y + 1) (i := i) (j := j).
      destruct IH as [y' Hy']; [ exact Hj | ].
      exists y'; split_top; (lia || tauto).
    + (* Line y is kept, at index i; the lines above come from the recursion. *)
      cbn [H L HW fst] in *.
      destruct (Z.eqb_spec j i) as [-> | Ej].
      * (* index i: line y of g, which is not full by EF *)
        exists y; split_top; (lia || assumption || reflexivity).
      * (* index above i: given by the induction hypothesis *)
        specialize IH with (y := y + 1) (i := i + 1) (j := j).
        destruct IH as [y' Hy']; [ lia | ].
        exists y'; split_top; (lia || tauto).
Qed.

Lemma FilterFullLinesSpec : ∀ (g : Grid) (fuel : ℕ) (y i : ℤ),
    0 ≤ H (FilterFullLines g fuel y i) ≤ Z.of_nat fuel
  ∧ (∀ j : ℤ,
       i ≤ j < i + H (FilterFullLines g fuel y i) →
       ∃ y' : ℤ,
           y ≤ y' < y + Z.of_nat fuel
         ∧ IsFullLineb g y' = false
         ∧ L (FilterFullLines g fuel y i) j = L g y').
Proof.
  intros; split_top; intros; (apply FilterFullLinesHeight || (apply FilterFullLinesRows; assumption)).
Qed.

Lemma ClearFullLinesBox : ∀ g : Grid,
  HW (ClearFullLines g) = HW g ∧ YX (ClearFullLines g) = YX g.
Proof.
  intros.
  assert (EW : W (FilterFullLines g (Z.to_nat (H g)) (Y g) (Y g)) = W g)
    by apply FilterFullLinesBox.
  assert (EYX : YX (FilterFullLines g (Z.to_nat (H g)) (Y g) (Y g)) = YX g)
    by apply FilterFullLinesBox.
  (* ClearFullLines resizes g2 to the height of g *)
  split; cbn; rewrite ?EW; (assumption || (symmetry; apply surjective_pairing)).
Qed.

(* After clearing, no line is full: a kept line is a non-full line of g (same
 * row function, same X and W), and a line added on top is empty, hence not
 * full since the grid is at least one block wide. *)
Lemma ClearFullLinesNoFullLine : ∀ (g : Grid)
  (H1 : 0 ≤ H g)
  (H2 : 0 < W g),
  ¬ HasFullLine (ClearFullLines g).
Proof.
  intros; intros [j Hj].
  assert (Hjr : Y (ClearFullLines g) ≤ j < Y (ClearFullLines g) + H (ClearFullLines g))
    by tauto.
  assert (HFull : IsFullLine (ClearFullLines g) j) by tauto.
  unfold IsFullLine in HFull.
  (* The cleared grid has g's box... *)
  assert (EHW : HW (ClearFullLines g) = HW g) by apply ClearFullLinesBox.
  assert (EYX : YX (ClearFullLines g) = YX g) by apply ClearFullLinesBox.
  unfold Y, X, H, W in Hjr, HFull; rewrite EHW, EYX in Hjr, HFull.
  fold (Y g) (X g) (H g) (W g) in Hjr, HFull.
  (* ... and its lines are those of g2, then empty ones. *)
  unfold ClearFullLines, Resize in HFull; cbn [L] in HFull.
  set (g2 := FilterFullLines g (Z.to_nat (H g)) (Y g) (Y g)) in *.
  assert (EY2 : Y g2 = Y g) by (unfold Y; f_equal; apply FilterFullLinesBox).
  destruct (Z.ltb_spec j (Y g2 + H g2)) as [Hlt | Hge].
  - (* j is a line copied from g, which is not full *)
    assert (Hj2 : Y g ≤ j < Y g + H g2) by lia.
    edestruct FilterFullLinesRows as [y' Hy']; [ exact Hj2 | ].
    assert (HFb : IsFullLineb g y' = false) by tauto.
    assert (HLrow : L g2 j = L g y') by tauto.
    assert (HNotFull : ¬ IsFullLine g y') by (apply IsFullLinebFalseElim; exact HFb).
    apply HNotFull; intros x Hx.
    rewrite <- HLrow; apply HFull; exact Hx.
  - (* j is a line added on top, and it is empty *)
    discriminate (HFull (X g) ltac:(lia)).
Qed.


(* ========================================================================= *)
(* Events: what they change, and the Valid they establish                    *)
(* ========================================================================= *)

(* An event step-function reads "if guard then Some s2 else None". On a
 * successful step, [step_inv] splits the guard into hypotheses and replaces
 * the next state by s2. *)
#[local] Ltac step_inv H :=
  match type of H with
  | (if ?c then _ else _) = Some _ =>
      let E := fresh "E" in
      destruct c eqn: E; [ | discriminate H ];
      inject H; subst; rewrite ?andb_true_iff, ?negb_true_iff in E
  end.

(* A successful move is a relocation of the piece to a Valid position. *)
Lemma MovePieceOK : ∀ dy dx s s'
  (H1 : MovePiece (dy, dx) s = Some s'),
    gameover s = false
  ∧ Valid (mg s) (p s) (py s + dy, px s + dx) (pr s) = true
  ∧ s' = NewPieceYXState (py s + dy, px s + dx) s.
Proof.
  intros; cbv beta iota zeta delta [MovePiece CanMovePiece] in H1.
  step_inv H1; tauto.
Qed.

Lemma MovePieceUnchanged : ∀ dyx s s'
  (H1 : MovePiece dyx s = Some s'),
    mg s' = mg s ∧ p s' = p s ∧ pr s' = pr s ∧ gameover s' = gameover s.
Proof.
  intros; destruct dyx as [dy dx].
  assert (E : s' = NewPieceYXState (py s + dy, px s + dx) s)
    by (apply MovePieceOK in H1; tauto).
  subst; now split_top.
Qed.

Lemma MovePieceValid : ∀ dyx s s'
  (H1 : MovePiece dyx s = Some s'),
  Valid (mg s') (p s') (pyx s') (pr s') = true.
Proof.
  intros; destruct dyx as [dy dx].
  assert (E : s' = NewPieceYXState (py s + dy, px s + dx) s)
    by (apply MovePieceOK in H1; tauto).
  assert (HV : Valid (mg s) (p s) (py s + dy, px s + dx) (pr s) = true)
    by (apply MovePieceOK in H1; tauto).
  subst; exact HV.
Qed.

(* A successful MovePiece proves its own guard held. *)
Lemma MovePieceNotGameover : ∀ [s s' dyx]
  (H1 : MovePiece dyx s = Some s'),
  gameover s = false.
Proof.
  intros; destruct dyx as [dy dx]; apply MovePieceOK in H1; tauto.
Qed.

Lemma RotatePieceOK : ∀ cw s s'
  (H1 : RotatePiece cw s = Some s'),
    mg s' = mg s
  ∧ p s' = p s
  ∧ pyx s' = pyx s
  ∧ gameover s' = gameover s
  ∧ pr s' = (pr s + (if cw then -1 else 1)) mod 4.
Proof.
  intros; cbv beta zeta delta [RotatePiece] in H1.
  step_inv H1; now split_top.
Qed.

Lemma RotatePieceValid : ∀ cw s s'
  (H1 : RotatePiece cw s = Some s'),
  Valid (mg s') (p s') (pyx s') (pr s') = true.
Proof.
  intros; cbv beta zeta delta [RotatePiece] in H1.
  step_inv H1; tauto.
Qed.

(* A successful RotatePiece proves its own guard held. *)
Lemma RotatePieceNotGameover : ∀ [s s' cw]
  (H1 : RotatePiece cw s = Some s'),
  gameover s = false.
Proof.
  intros; cbv beta zeta delta [RotatePiece] in H1.
  step_inv H1; tauto.
Qed.

Lemma FixPieceOK : ∀ pNew s s'
  (H1 : FixPiece pNew s = Some s'),
    mg s' = ClearFullLines ((mg s ∪ (PieceGrid s ⊕ pyx s)) ∩ Full (mg s))
  ∧ p s' = pNew
  ∧ pyx s' = InitialYX pNew
  ∧ pr s' = 0
  ∧ gameover s' = (ForbiddenGrid ∩ mg s' ⊈ ∅).
Proof.
  intros; cbv beta zeta delta [FixPiece] in H1.
  step_inv H1; now split_top.
Qed.


(* ========================================================================= *)
(* Piece invariants                                                          *)
(* ========================================================================= *)

(* The two piece invariants are precisely the two conjuncts of Valid. *)
Lemma ValidPieceInvariants : ∀ (s : State)
  (HV : Valid (mg s) (p s) (pyx s) (pr s) = true),
  PieceOccupiedInsideBounds s ∧ PieceOnFreeBlocks s.
Proof.
  intros; unfold Valid, PieceOccupiedInsideBounds, PieceOnFreeBlocks, PieceGrid in *.
  rewrite andb_true_iff in HV; tauto.
Qed.

Definition NewPieceGrid (p : Piece) : Grid :=
  RotGrid p 0 ⊕ InitialYX p.

(* A newly chosen piece appears in the forbidden zone (AxiomsRotGrid). *)
Lemma NewPieceInForbiddenGrid : ∀ pNew : Piece,
  NewPieceGrid pNew ⊆ ForbiddenGrid = true.
Proof.
  intros; apply AxiomsRotGrid.
Qed.

(* A newly chosen piece appears in the forbidden zone, hence inside any grid
 * having the main grid's box, and on free blocks as long as the forbidden zone
 * is free, i.e. as long as the game is not over. *)
Lemma NewPieceInsideBounds : ∀ (pNew : Piece) (g : Grid)
  (EHW : HW g = HW InitialMainGrid)
  (EYX : YX g = YX InitialMainGrid),
  NewPieceGrid pNew ⊆ Full g = true.
Proof.
  intros; rewrite FullBoxEq with (g2 := InitialMainGrid) by assumption.
  assert (HF : Full ForbiddenGrid ⊆ Full InitialMainGrid = true)
    by apply AxiomsForbiddenGrid.
  apply GridIncludeTransitive with (g2 := ForbiddenGrid).
  all: (apply NewPieceInForbiddenGrid || (apply GridIncludeFullImpliesNonFull; assumption)).
Qed.

Lemma NewPieceFree : ∀ (pNew : Piece) (g : Grid)
  (H1 : ForbiddenGrid ∩ g ⊆ ∅ = true),
  NewPieceGrid pNew ∩ g ⊆ ∅ = true.
Proof.
  intros; apply GridIncludeTransitive with (g2 := ForbiddenGrid ∩ g).
  all: (assumption || (apply GridIntersectMonotoneLeft, NewPieceInForbiddenGrid)).
Qed.

(* A state whose piece was just spawned satisfies both piece invariants, as
 * long as its main grid has the initial box, and occupied blocks in the
 * forbidden zone imply gameover (the ← direction of Gameover). *)
Lemma NewPieceInvariants : ∀ s
  (Epyx : pyx s = InitialYX (p s))
  (Epr : pr s = 0)
  (EHW : HW (mg s) = HW InitialMainGrid)
  (EYX : YX (mg s) = YX InitialMainGrid)
  (HG : ForbiddenGrid ∩ mg s ⊈ ∅ = true → gameover s = true),
  PieceOccupiedInsideBounds s ∧ PieceOnFreeBlocks s.
Proof.
  intros.
  unfold PieceOccupiedInsideBounds, PieceOnFreeBlocks, PieceGrid; rewrite Epyx, Epr.
  change (RotGrid (p s) 0 ⊕ InitialYX (p s)) with (NewPieceGrid (p s)).
  assert (HB : NewPieceGrid (p s) ⊆ Full (mg s) = true)
    by (apply NewPieceInsideBounds; assumption).
  assert (HF : gameover s = false → NewPieceGrid (p s) ∩ mg s ⊆ ∅ = true). {
    intros HGo; apply NewPieceFree.
    (* Not gameover: by HG, the forbidden zone is free. *)
    destruct (ForbiddenGrid ∩ mg s ⊆ ∅); [ reflexivity | now rewrite HG in HGo ].
  }
  split; assumption.
Qed.


(* ========================================================================= *)
(* SpecCorrect (safety)                                                      *)
(* ========================================================================= *)

Lemma CorrectSpec : ∀ s,
  Correct s ↔ (
    TypeOK s
  ∧ PieceOccupiedInsideBounds s
  ∧ PieceOnFreeBlocks s
  ∧ NoFullLine s
  ∧ Gameover s).
Proof.
  intros; unfold Correct, CorrectWithoutGameover; tauto.
Qed.

Lemma TypeOKSpec : ∀ s
  (HT : TypeOK s),
    HW (mg s) = HW InitialMainGrid
  ∧ YX (mg s) = YX InitialMainGrid
  ∧ 0 ≤ pr s ≤ 3.
Proof.
  intros; unfold TypeOK in HT; tauto.
Qed.

(***************)
(* InitCorrect *)
(***************)

Lemma InitCorrect : ∀ p : Piece, Correct (Init p).
Proof.
  intros.
  assert (HPiece : PieceOccupiedInsideBounds (Init p) ∧ PieceOnFreeBlocks (Init p))
    by (apply NewPieceInvariants; easy).
  assert (HN : NoFullLine (Init p)). {
    (* By the axiom on the initial main grid, whose origin is 0. *)
    assert (EYX : YX InitialMainGrid = (0, 0)) by apply AxiomsInitialMainGrid.
    assert (HNoFull : ∀ y : ℤ, 0 ≤ y < H InitialMainGrid → ¬ IsFullLine InitialMainGrid y)
      by apply AxiomsInitialMainGrid.
    intros [y Hy]; cbn [Init mg] in Hy.
    assert (Hr : 0 ≤ y < H InitialMainGrid)
      by (unfold Y in Hy; rewrite EYX in Hy; cbn in Hy; lia).
    assert (HFull : IsFullLine InitialMainGrid y) by tauto.
    eapply HNoFull; eassumption.
  }
  apply CorrectSpec; split_top; (tauto || easy).
Qed.

(***************)
(* NextCorrect *)
(***************)

(**** MovePieceCorrect, and relocation in general ****)

(* Relocating the current piece to a Valid position preserves the invariants:
 * the piece ones are Valid's conjuncts, and the others hold by conversion,
 * since they read only mg, pr and gameover, which are unchanged. *)
Lemma NewPieceYXStateCorrectWithoutGameover : ∀ (pyxNew : ℤ × ℤ) (s : State)
  (H1 : TypeOK s)
  (H2 : NoFullLine s)
  (H3 : Valid (mg s) (p s) pyxNew (pr s) = true),
  CorrectWithoutGameover (NewPieceYXState pyxNew s).
Proof.
  intros.
  assert (HPiece : PieceOccupiedInsideBounds (NewPieceYXState pyxNew s)
                 ∧ PieceOnFreeBlocks (NewPieceYXState pyxNew s))
    by (apply ValidPieceInvariants; exact H3).
  unfold CorrectWithoutGameover; split_top; (assumption || tauto).
Qed.

Lemma MovePieceCorrectWithoutGameover : ∀ [s s' dyx]
  (H1 : CorrectWithoutGameover s)
  (H2 : MovePiece dyx s = Some s'),
  CorrectWithoutGameover s'.
Proof.
  intros; destruct dyx as [dy dx].
  assert (HT : TypeOK s) by (unfold CorrectWithoutGameover in H1; tauto).
  assert (HN : NoFullLine s) by (unfold CorrectWithoutGameover in H1; tauto).
  assert (E : s' = NewPieceYXState (py s + dy, px s + dx) s)
    by (apply MovePieceOK in H2; tauto).
  assert (HV : Valid (mg s) (p s) (py s + dy, px s + dx) (pr s) = true)
    by (apply MovePieceOK in H2; tauto).
  subst; apply NewPieceYXStateCorrectWithoutGameover; assumption.
Qed.

Lemma MovePieceGameover : ∀ [s s' dyx]
  (H1 : Correct s)
  (H2 : MovePiece dyx s = Some s'),
  Gameover s'.
Proof.
  intros; destruct dyx as [dy dx].
  assert (HG : Gameover s) by (unfold Correct in H1; tauto).
  assert (E : s' = NewPieceYXState (py s + dy, px s + dx) s)
    by (apply MovePieceOK in H2; tauto).
  subst; exact HG.
Qed.

Lemma MovePieceCorrect : ∀ [s s' dyx]
  (H1 : Correct s)
  (H2 : MovePiece dyx s = Some s'),
  Correct s'.
Proof.
  intros.
  assert (HCwg : CorrectWithoutGameover s) by (unfold Correct in H1; tauto).
  assert (HCwg' : CorrectWithoutGameover s') by eapp MovePieceCorrectWithoutGameover.
  assert (HG' : Gameover s') by eapp MovePieceGameover.
  split; assumption.
Qed.

(**** RotatePieceCorrect ****)

(* Rotating needs neither piece invariant beforehand: its success
 * re-establishes both, via Valid at the new rotation. *)
Lemma RotatePieceInvariants : ∀ cw s s'
  (H1 : TypeOK s)
  (H2 : NoFullLine s)
  (H3 : RotatePiece cw s = Some s'),
  CorrectWithoutGameover s'.
Proof.
  intros.
  assert (Emg : mg s' = mg s) by (apply RotatePieceOK in H3; tauto).
  assert (Epr : pr s' = (pr s + (if cw then -1 else 1)) mod 4)
    by (apply RotatePieceOK in H3; tauto).
  assert (HPiece : PieceOccupiedInsideBounds s' ∧ PieceOnFreeBlocks s')
    by (apply ValidPieceInvariants; eapp RotatePieceValid).
  pose proof (Z.mod_pos_bound (pr s + (if cw then -1 else 1)) 4 ltac:(lia)).
  unfold CorrectWithoutGameover, TypeOK, NoFullLine in *; rewrite Emg, Epr.
  repeat split; (tauto || lia).
Qed.

Lemma RotatePieceCorrectWithoutGameover : ∀ [s s' cw]
  (H1 : CorrectWithoutGameover s)
  (H2 : RotatePiece cw s = Some s'),
  CorrectWithoutGameover s'.
Proof.
  intros.
  assert (HT : TypeOK s) by (unfold CorrectWithoutGameover in H1; tauto).
  assert (HN : NoFullLine s) by (unfold CorrectWithoutGameover in H1; tauto).
  eapp RotatePieceInvariants.
Qed.

Lemma RotatePieceGameover : ∀ [s s' cw]
  (H1 : Correct s)
  (H2 : RotatePiece cw s = Some s'),
  Gameover s'.
Proof.
  intros.
  assert (HG : Gameover s) by (unfold Correct in H1; tauto).
  assert (Emg : mg s' = mg s) by (apply RotatePieceOK in H2; tauto).
  assert (Ego : gameover s' = gameover s) by (apply RotatePieceOK in H2; tauto).
  unfold Gameover in *; rewrite Emg, Ego; exact HG.
Qed.

Lemma RotatePieceCorrect : ∀ [s s' dyx]
  (H1 : Correct s)
  (H2 : RotatePiece dyx s = Some s'),
  Correct s'.
Proof.
  intros.
  assert (HCwg : CorrectWithoutGameover s) by (unfold Correct in H1; tauto).
  assert (HCwg' : CorrectWithoutGameover s') by eapp RotatePieceCorrectWithoutGameover.
  assert (HG' : Gameover s') by eapp RotatePieceGameover.
  split; assumption.
Qed.

(**** FixPieceCorrect ****)

Lemma FixPieceCorrectWithoutGameover : ∀ [s s' pNew]
  (H1 : CorrectWithoutGameover s)
  (H2 : FixPiece pNew s = Some s'),
  CorrectWithoutGameover s'.
Proof.
  intros.
  assert (EHW : HW (mg s) = HW InitialMainGrid)
    by (unfold CorrectWithoutGameover, TypeOK in H1; tauto).
  assert (EYX : YX (mg s) = YX InitialMainGrid)
    by (unfold CorrectWithoutGameover, TypeOK in H1; tauto).
  set (u := (mg s ∪ PieceGrid s ⊕ pyx s) ∩ Full (mg s)).
  assert (Emg : mg s' = ClearFullLines u) by (apply FixPieceOK in H2; tauto).
  assert (Ep : p s' = pNew) by (apply FixPieceOK in H2; tauto).
  assert (Epyx : pyx s' = InitialYX pNew) by (apply FixPieceOK in H2; tauto).
  assert (Epr : pr s' = 0) by (apply FixPieceOK in H2; tauto).
  assert (Ego : gameover s' = (ForbiddenGrid ∩ mg s' ⊈ ∅))
    by (apply FixPieceOK in H2; tauto).
  (* The clamped union, then the clearing, both keep the box of mg s. *)
  assert (B1 : HW u = HW (mg s)) by apply BoxUnionClamp.
  assert (B2 : YX u = YX (mg s)) by apply BoxUnionClamp.
  assert (C1 : HW (ClearFullLines u) = HW u) by apply ClearFullLinesBox.
  assert (C2 : YX (ClearFullLines u) = YX u) by apply ClearFullLinesBox.
  assert (EHW' : HW (mg s') = HW InitialMainGrid) by congruence.
  assert (EYX' : YX (mg s') = YX InitialMainGrid) by congruence.
  assert (HPiece : PieceOccupiedInsideBounds s' ∧ PieceOnFreeBlocks s')
    by (apply NewPieceInvariants; congruence).
  assert (HT' : TypeOK s')
    by (unfold TypeOK; rewrite Epr; split_top; (assumption || lia)).
  assert (HN' : NoFullLine s'). {
    (* The box of u has the initial main grid's positive dimensions. *)
    assert (HPosH : H InitialMainGrid > 0) by apply AxiomsInitialMainGrid.
    assert (HPosW : W InitialMainGrid > 0) by apply AxiomsInitialMainGrid.
    unfold NoFullLine; rewrite Emg; apply ClearFullLinesNoFullLine;
      unfold H, W; rewrite B1, EHW; fold (H InitialMainGrid) (W InitialMainGrid); lia.
  }
  unfold CorrectWithoutGameover; split_top; (assumption || tauto).
Qed.

Lemma FixPieceGameover : ∀ [s s' pNew]
  (H1 : Correct s)
  (H2 : FixPiece pNew s = Some s'),
  Gameover s'.
Proof.
  intros.
  (* gameover s' is *defined* as the forbidden zone meeting the new main grid. *)
  assert (Ego : gameover s' = (ForbiddenGrid ∩ mg s' ⊈ ∅))
    by (apply FixPieceOK in H2; tauto).
  unfold Gameover; rewrite Ego; tauto.
Qed.

Lemma FixPieceCorrect : ∀ s s' pNew
  (H1 : Correct s)
  (H2 : FixPiece pNew s = Some s'),
  Correct s'.
Proof.
  intros.
  assert (HCwg : CorrectWithoutGameover s) by (unfold Correct in H1; tauto).
  assert (HCwg' : CorrectWithoutGameover s') by eapp FixPieceCorrectWithoutGameover.
  assert (HG' : Gameover s') by eapp FixPieceGameover.
  split; assumption.
Qed.

(**** FallStepCorrect ****)

(* A fall step is a move down, or a fix. Nothing to prove per invariant. *)
Lemma FallStepCorrect : ∀ s s' pNew
  (H1 : Correct s)
  (H2 : FallStep pNew s = Some s'),
  Correct s'.
Proof.
  intros; unfold FallStep in H2.
  destruct (MovePiece (-1, 0) s) eqn: E.
  - inject H2; subst; eapp MovePieceCorrect.
  - eapp FixPieceCorrect.
Qed.

(**** StutterCorrect ****)

Lemma StutterCorrect : ∀ s s'
  (H1 : Correct s)
  (H2 : Next Stutter s = Some s'),
  Correct s'.
Proof.
  intros; now inject H2; subst.
Qed.


Lemma NextCorrect : ∀ s s' e
  (H1 : Correct s)
  (H2 : Next e s = Some s'),
  Correct s'.
Proof.
  intros; destruct e; eauto using MovePieceCorrect, RotatePieceCorrect,
    FixPieceCorrect, FallStepCorrect, StutterCorrect.
Qed.

Lemma SpecCorrect :
    (∀ p, Correct (Init p))
  ∧ (∀ s s' e, Correct s → Next e s = Some s' → Correct s').
Proof.
  split; eauto using InitCorrect, NextCorrect.
Qed.


(* ========================================================================= *)
(* FallStepAlwaysSucceeds (liveness)                                         *)
(* ========================================================================= *)

Lemma FallStepAlwaysSucceeds : ∀ s pNew
  (H1 : gameover s = false),
  ∃ s', FallStep pNew s = Some s'.
Proof.
  intros; cbv beta iota zeta delta [FallStep MovePiece FixPiece].
  rewrite H1; cbn [negb andb].
  destruct (CanMovePiece (-1, 0) s); eexists; reflexivity.
Qed.


(* ========================================================================= *)
(* Helpers for refining models                                               *)
(* ========================================================================= *)

(* Choosing a new current piece, while occupied blocks in the forbidden zone
 * imply gameover (the only part of Gameover needed), preserves
 * CorrectWithoutGameover. *)
Lemma NewPieceStateCorrectWithoutGameover : ∀ (pNew : Piece) (s : State)
  (H1 : CorrectWithoutGameover s)
  (H2 : ForbiddenGrid ∩ mg s ⊈ ∅ = true → gameover s = true),
  CorrectWithoutGameover (NewPieceState pNew s).
Proof.
  intros.
  assert (EHW : HW (mg s) = HW InitialMainGrid)
    by (unfold CorrectWithoutGameover, TypeOK in H1; tauto).
  assert (EYX : YX (mg s) = YX InitialMainGrid)
    by (unfold CorrectWithoutGameover, TypeOK in H1; tauto).
  assert (HN : NoFullLine s) by (unfold CorrectWithoutGameover in H1; tauto).
  assert (HPiece : PieceOccupiedInsideBounds (NewPieceState pNew s)
                 ∧ PieceOnFreeBlocks (NewPieceState pNew s))
    by (apply NewPieceInvariants; (reflexivity || assumption)).
  unfold CorrectWithoutGameover, TypeOK; repeat split; (assumption || tauto || (cbn; lia)).
Qed.

(* Choosing a new current piece preserves Correct. This is the T1 content of any
 * higher-level event that spawns a piece without touching the main grid — T3's
 * HoldPiece, and later T4's preview pop. *)
Lemma NewPieceStateCorrect : ∀ (pNew : Piece) (s : State)
  (H1 : Correct s),
  Correct (NewPieceState pNew s).
Proof.
  intros.
  assert (HCwg : CorrectWithoutGameover s) by (unfold Correct in H1; tauto).
  assert (HG : Gameover s) by (unfold Correct in H1; tauto).
  assert (HCwg' : CorrectWithoutGameover (NewPieceState pNew s))
    by (apply NewPieceStateCorrectWithoutGameover; (assumption || apply HG)).
  (* Gameover only reads mg and gameover, which are unchanged. *)
  split; assumption.
Qed.

(* Relocating the current piece (same p, same pr) preserves Correct, given the
 * target position is already Valid. Used by T5's DropPiece, whose target
 * position is exactly the one LowestShadowY certifies as Valid. *)
Lemma NewPieceYXStateCorrect : ∀ (pyxNew : ℤ × ℤ) (s : State)
  (H1 : Correct s)
  (H2 : Valid (mg s) (p s) pyxNew (pr s) = true),
  Correct (NewPieceYXState pyxNew s).
Proof.
  intros.
  assert (HT : TypeOK s) by (unfold Correct, CorrectWithoutGameover in H1; tauto).
  assert (HN : NoFullLine s) by (unfold Correct, CorrectWithoutGameover in H1; tauto).
  assert (HG : Gameover s) by (unfold Correct in H1; tauto).
  assert (HCwg' : CorrectWithoutGameover (NewPieceYXState pyxNew s))
    by (apply NewPieceYXStateCorrectWithoutGameover; assumption).
  (* Gameover only reads mg and gameover, which are unchanged. *)
  split; assumption.
Qed.

(* Below the theoretical floor (py < 1-PW), no piece can ever be Valid,
 * regardless of its shape or rotation: AxiomsRotGrid guarantees at least one
 * occupied local cell, and pushing the whole piece low enough forces that
 * cell's absolute row below the main grid's own row 0 (given Y g = 0), failing
 * the "occupied ⊆ Full g" conjunct of Valid. Used to size ShadowY's fuel. *)
Lemma ValidBelowFloor : ∀ (g : Grid) (pc : Piece) (py px pr : ℤ)
  (HY : Y g = 0)
  (HR : 0 ≤ pr < 4)
  (HP : py < 1 - PW),
  Valid g pc (py, px) pr = false.
Proof.
  intros; apply not_true_iff_false; intros HV.
  assert (HIn : RotGrid pc pr ⊕ (py, px) ⊆ Full g = true)
    by (unfold Valid in HV; rewrite andb_true_iff in HV; tauto).
  assert (EHW : HW (RotGrid pc pr) = (PW, PW)) by (apply AxiomsRotGrid; exact HR).
  assert (EYX : YX (RotGrid pc pr) = (0, 0)) by (apply AxiomsRotGrid; exact HR).
  assert (Hocc : ∃ y x : ℤ, 0 ≤ y < PW ∧ 0 ≤ x < PW ∧ L (RotGrid pc pr) y x = true)
    by (apply AxiomsRotGrid; exact HR).
  (* The occupied local cell (ry, rx) is the block (py + ry, px + rx) of the
   * translated piece, which must then lie in g's box. *)
  destruct Hocc as (ry & rx & Hocc).
  assert (Hb : InBox (RotGrid pc pr ⊕ (py, px)) (py + ry) (px + rx) = true)
    by (apply InBoxTrue; unfold GridTranslate, Y, X, H, W; cbn; rewrite EHW, EYX; cbn; lia).
  assert (Hl : L (RotGrid pc pr ⊕ (py, px)) (py + ry) (px + rx) = true)
    by (cbn; rewrite !Z.add_simpl_l; tauto).
  assert (HboxFull : InBox (Full g) (py + ry) (px + rx) = true)
    by (apply GridIncludeElim with (g1 := RotGrid pc pr ⊕ (py, px)); assumption).
  apply InBoxTrue in HboxFull; unfold Y, X, H, W in *; cbn in HboxFull; lia.
Qed.

(* Rotating after an arbitrary relocation preserves Correct, needing only the
 * three "shape" conjuncts of Correct at the pre-relocation state (TypeOK,
 * Gameover, NoFullLine), not PieceOccupiedInsideBounds/PieceOnFreeBlocks.
 * This matters for wall kicks (T6): NewPieceYXState may relocate the piece to
 * a position that is not itself Valid at the current pr (that is the whole
 * point of a kick: the relocation is a mere candidate, validated only by
 * whether the subsequent rotation succeeds), so Correct of the relocated,
 * unrotated state cannot in general be assumed. RotatePieceInvariants does
 * not need it either. The extra `gameover s' = gameover s` conclusion is
 * exposed because it is needed again, unchanged, by callers threading this
 * fact up through further layers (T6Proofs.v, for a
 * GameoverImplyNotSwapped-style invariant). *)
Lemma RotateAfterRelocateCorrect : ∀ (pyxNew : ℤ × ℤ) (cw : bool) (s s' : State)
  (H1 : TypeOK s)
  (H2 : Gameover s)
  (H3 : NoFullLine s)
  (Hn : RotatePiece cw (NewPieceYXState pyxNew s) = Some s'),
  Correct s' ∧ gameover s' = gameover s.
Proof.
  intros.
  assert (Emg : mg s' = mg s) by (apply RotatePieceOK in Hn; tauto).
  assert (Ego : gameover s' = gameover s) by (apply RotatePieceOK in Hn; tauto).
  assert (HCwg' : CorrectWithoutGameover s')
    by (apply RotatePieceInvariants with (s := NewPieceYXState pyxNew s) (cw := cw); assumption).
  assert (HG' : Gameover s') by (unfold Gameover in *; rewrite Emg, Ego; exact H2).
  assert (HC' : Correct s') by (split; assumption).
  split; assumption.
Qed.

(* Same as RotateAfterRelocateCorrect, but from CorrectWithoutGameover instead
 * of full Correct. *)
Lemma RotateAfterRelocateCorrectWithoutGameover : ∀ (pyxNew : ℤ × ℤ) (cw : bool) (s s' : State)
  (H1 : CorrectWithoutGameover s)
  (Hn : RotatePiece cw (NewPieceYXState pyxNew s) = Some s'),
  CorrectWithoutGameover s' ∧ gameover s' = gameover s ∧ mg s' = mg s.
Proof.
  intros.
  assert (HT : TypeOK s) by (unfold CorrectWithoutGameover in H1; tauto).
  assert (HN : NoFullLine s) by (unfold CorrectWithoutGameover in H1; tauto).
  assert (Emg : mg s' = mg s) by (apply RotatePieceOK in Hn; tauto).
  assert (Ego : gameover s' = gameover s) by (apply RotatePieceOK in Hn; tauto).
  assert (HCwg' : CorrectWithoutGameover s')
    by (apply RotatePieceInvariants with (s := NewPieceYXState pyxNew s) (cw := cw); assumption).
  split_top; assumption.
Qed.
