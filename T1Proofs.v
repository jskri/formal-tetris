(* We make logical classical. This is OK since we do not use the
 * computational content of proofs (no program extraction). *)
From Stdlib Require Import Classical Lia Bool Setoid.
From Hammer Require Import Tactics.
From Tetris Require Import T1 Notations Quantifiers QuantifiersProofs.


(* ========================================================================= *)
(* Reflection: from the boolean quantifiers to logical ones                  *)
(* ========================================================================= *)

(* This is the only section where [forallbz2], and hence [seqz], is unfolded.
 * Everything above it speaks of boxes and occupied blocks. *)

Lemma InRangeTrue : ∀ a b c : ℤ, (a ≤? b <? c) = true ↔ a ≤ b < c.
Proof.
  intros a b c; rewrite andb_true_iff, Z.leb_le, Z.ltb_lt; tauto.
Qed.

Lemma InBoxTrue : ∀ (g : Grid) (y x : ℤ),
  InBox g y x = true ↔ (Y g ≤ y < Y g + H g) ∧ (X g ≤ x < X g + W g).
Proof.
  intros g y x; unfold InBox; rewrite andb_true_iff, !InRangeTrue; tauto.
Qed.

(* The empty grid has an empty box, hence no block at all. *)
Lemma InBoxEmpty : ∀ y x : ℤ, InBox ∅ y x = false.
Proof.
  intros y x; apply not_true_is_false; intro Hb.
  apply InBoxTrue in Hb.
  unfold EmptyGrid, Y, X, H, W in Hb; simpl in Hb; lia.
Qed.

(* [g1 ⊆ g2] says: every occupied block of g1's box is a block of g2's box, and
 * is occupied there. Note the box membership of g2 in the conclusion: it is
 * what makes ⊆ transitive. *)
Lemma GridIncludeSpec : ∀ g1 g2 : Grid,
  g1 ⊆ g2 = true ↔
  (∀ y x : ℤ,
     InBox g1 y x = true → L g1 y x = true → InBox g2 y x = true ∧ L g2 y x = true).
Proof.
  intros g1 g2; unfold GridInclude; rewrite forallbz2Forall; split.
  - intros Hall y x Hb1 Hl1.
    apply InBoxTrue in Hb1 as [Hy Hx].
    specialize (Hall y x Hy Hx).
    rewrite Hl1 in Hall; simpl in Hall.
    apply andb_true_iff in Hall as [Hb2 Hl2].
    split; (exact Hb2 || exact Hl2).
  - intros Hall y x Hy Hx.
    destruct (L g1 y x) eqn: Hl1; simpl; [ | reflexivity ].
    assert (Hb1 : InBox g1 y x = true) by (apply InBoxTrue; split; assumption).
    destruct (Hall y x Hb1 Hl1) as [Hb2 Hl2].
    apply andb_true_iff; split; (exact Hb2 || exact Hl2).
Qed.

Lemma GridIncludeIntro : ∀ g1 g2 : Grid,
  (∀ y x : ℤ,
     InBox g1 y x = true → L g1 y x = true → InBox g2 y x = true ∧ L g2 y x = true) →
  g1 ⊆ g2 = true.
Proof.
  intros g1 g2 Hall; apply (proj2 (GridIncludeSpec g1 g2)); exact Hall.
Qed.

Lemma GridIncludeElim : ∀ g1 g2 : Grid,
  g1 ⊆ g2 = true →
  ∀ y x : ℤ,
    InBox g1 y x = true → L g1 y x = true → InBox g2 y x = true ∧ L g2 y x = true.
Proof.
  intros g1 g2 H1; apply (proj1 (GridIncludeSpec g1 g2)); exact H1.
Qed.

(* [g ⊆ ∅] is not set inclusion: since ∅'s box is empty, it says exactly that
 * g has no occupied block in its own box. *)
Lemma GridIncludeEmptyIntro : ∀ g : Grid,
  (∀ y x : ℤ, InBox g y x = true → L g y x = false) → g ⊆ ∅ = true.
Proof.
  intros g Hg; apply GridIncludeIntro; intros y x Hb Hl.
  rewrite (Hg y x Hb) in Hl; discriminate Hl.
Qed.

Lemma GridIncludeEmptyElim : ∀ g : Grid,
  g ⊆ ∅ = true → ∀ y x : ℤ, InBox g y x = true → L g y x = false.
Proof.
  intros g Hg y x Hb.
  destruct (L g y x) eqn: Hl; [ | reflexivity ].
  destruct (GridIncludeElim g ∅ Hg y x Hb Hl) as [Hb2 _].
  rewrite InBoxEmpty in Hb2; discriminate Hb2.
Qed.

Lemma IsFullLinebFalseElim : ∀ (g : Grid) (y : ℤ),
  IsFullLineb g y = false → ¬ IsFullLine g y.
Proof.
  intros g y HF HFull; unfold IsFullLineb in HF.
  destruct (Y g ≤? y <? Y g + H g) eqn: EG; simpl in HF.
  - assert (E : forallbz (L g y) (seqz (X g) (W g)) = true)
      by (apply forallbzIntro; intros x Hx; exact (HFull x Hx)).
    rewrite E in HF; discriminate HF.
  - discriminate HF.
Qed.


(* ========================================================================= *)
(* Box algebra                                                               *)
(* ========================================================================= *)

Lemma HWEq : ∀ g1 g2 : Grid, H g1 = H g2 → W g1 = W g2 → HW g1 = HW g2.
Proof.
  intros g1 g2 E1 E2; unfold H, W in E1, E2.
  rewrite (surjective_pairing (HW g1)), (surjective_pairing (HW g2)), E1, E2.
  reflexivity.
Qed.

Lemma YXEq : ∀ g1 g2 : Grid, Y g1 = Y g2 → X g1 = X g2 → YX g1 = YX g2.
Proof.
  intros g1 g2 E1 E2; unfold Y, X in E1, E2.
  rewrite (surjective_pairing (YX g1)), (surjective_pairing (YX g2)), E1, E2.
  reflexivity.
Qed.

(* [Full g] depends on g's box only, hence Full is box-extensional. *)
Lemma FullBoxEq : ∀ g1 g2 : Grid,
  HW g1 = HW g2 → YX g1 = YX g2 → Full g1 = Full g2.
Proof.
  intros g1 g2 E1 E2; unfold Full, Constant; rewrite E1, E2; reflexivity.
Qed.

(* The box of an intersection is the intersection of the boxes. This is what
 * makes ∩ the meet of ⊆, unconditionally. *)
Lemma InBoxIntersectTrue : ∀ (g1 g2 : Grid) (y x : ℤ),
  InBox (g1 ∩ g2) y x = true ↔ InBox g1 y x = true ∧ InBox g2 y x = true.
Proof.
  intros g1 g2 y x.
  assert (EY : Y (g1 ∩ g2) = Z.max (Y g1) (Y g2)) by reflexivity.
  assert (EX : X (g1 ∩ g2) = Z.max (X g1) (X g2)) by reflexivity.
  assert (EH : H (g1 ∩ g2)
             = Z.min (Y g1 + H g1) (Y g2 + H g2) - Z.max (Y g1) (Y g2)) by reflexivity.
  assert (EW : W (g1 ∩ g2)
             = Z.min (X g1 + W g1) (X g2 + W g2) - Z.max (X g1) (X g2)) by reflexivity.
  rewrite !InBoxTrue, EY, EX, EH, EW; lia.
Qed.

Lemma GridIncludeTransitive : ∀ g1 g2 g3
  (H1 : g1 ⊆ g2 = true)
  (H2 : g2 ⊆ g3 = true),
  g1 ⊆ g3 = true.
Proof.
  intros g1 g2 g3 H1 H2; apply GridIncludeIntro; intros y x Hb1 Hl1.
  (* H1 gives membership in g2's box, which is exactly what H2 needs. *)
  destruct (GridIncludeElim g1 g2 H1 y x Hb1 Hl1) as [Hb2 Hl2].
  exact (GridIncludeElim g2 g3 H2 y x Hb2 Hl2).
Qed.

(* ⊆ is antitone in the content of its left argument, at a fixed box. *)
Lemma GridIncludeWeakenLeft : ∀ g1 g1' g2
  (EHW : HW g1' = HW g1)
  (EYX : YX g1' = YX g1)
  (EL : ∀ y x : ℤ, L g1' y x = true → L g1 y x = true)
  (H1 : g1 ⊆ g2 = true),
  g1' ⊆ g2 = true.
Proof.
  intros g1 g1' g2 EHW EYX EL H1; apply GridIncludeIntro; intros y x Hb1' Hl1'.
  assert (Hb1 : InBox g1 y x = true). {
    keep_only Hb1' EHW EYX.
    unfold InBox, Y, X, H, W in *; rewrite EHW, EYX in Hb1'; exact Hb1'.
  }
  exact (GridIncludeElim g1 g2 H1 y x Hb1 (EL y x Hl1')).
Qed.

Lemma GridIncludeFullImpliesNonFull : ∀ g1 g2
  (H1 : Full g1 ⊆ g2 = true),
  g1 ⊆ g2 = true.
Proof.
  intros.
  (* [Full g1] has g1's box and is everywhere occupied. *)
  apply (GridIncludeWeakenLeft (Full g1) g1 g2); now try reflexivity.
Qed.

Lemma GridIntersectMonotoneLeft : ∀ g1 g2 g3
  (H1 : g1 ⊆ g2 = true),
  g1 ∩ g3 ⊆ g2 ∩ g3 = true.
Proof.
  intros.
  assert (EL : ∀ ga gb : Grid, ∀ y x : ℤ, L (ga ∩ gb) y x = L ga y x && L gb y x)
    by (intros; reflexivity).
  apply GridIncludeIntro; intros y x Hb Hl.
  rewrite EL in Hl; apply andb_true_iff in Hl as [Hl1 Hl3].
  apply InBoxIntersectTrue in Hb as [Hb1 Hb3].
  destruct (GridIncludeElim g1 g2 H1 y x Hb1 Hl1) as [Hb2 Hl2].
  split.
  - apply InBoxIntersectTrue; split; assumption.
  - rewrite EL; apply andb_true_iff; split; assumption.
Qed.

(* Clamping a union back onto its left operand's box: the box arithmetic is
 * pure absorption, min (max a b) a = a and max (min a b) a = a. *)
Lemma YUnionClamp : ∀ g1 g2 : Grid, Y ((g1 ∪ g2) ∩ Full g1) = Y g1.
Proof.
  intros g1 g2.
  assert (E : Y ((g1 ∪ g2) ∩ Full g1) = Z.max (Z.min (Y g1) (Y g2)) (Y g1))
    by reflexivity.
  rewrite E; lia.
Qed.

Lemma XUnionClamp : ∀ g1 g2 : Grid, X ((g1 ∪ g2) ∩ Full g1) = X g1.
Proof.
  intros g1 g2.
  assert (E : X ((g1 ∪ g2) ∩ Full g1) = Z.max (Z.min (X g1) (X g2)) (X g1))
    by reflexivity.
  rewrite E; lia.
Qed.

Lemma HUnionClamp : ∀ g1 g2 : Grid, H ((g1 ∪ g2) ∩ Full g1) = H g1.
Proof.
  intros g1 g2.
  assert (E : H ((g1 ∪ g2) ∩ Full g1)
            = Z.min (Z.min (Y g1) (Y g2)
                     + (Z.max (Y g1 + H g1) (Y g2 + H g2) - Z.min (Y g1) (Y g2)))
                    (Y g1 + H g1)
              - Z.max (Z.min (Y g1) (Y g2)) (Y g1)) by reflexivity.
  rewrite E; lia.
Qed.

Lemma WUnionClamp : ∀ g1 g2 : Grid, W ((g1 ∪ g2) ∩ Full g1) = W g1.
Proof.
  intros g1 g2.
  assert (E : W ((g1 ∪ g2) ∩ Full g1)
            = Z.min (Z.min (X g1) (X g2)
                     + (Z.max (X g1 + W g1) (X g2 + W g2) - Z.min (X g1) (X g2)))
                    (X g1 + W g1)
              - Z.max (Z.min (X g1) (X g2)) (X g1)) by reflexivity.
  rewrite E; lia.
Qed.

Lemma BoxUnionClamp : ∀ g1 g2 : Grid,
    HW ((g1 ∪ g2) ∩ Full g1) = HW g1
  ∧ YX ((g1 ∪ g2) ∩ Full g1) = YX g1.
Proof.
  intros g1 g2; split.
  - apply HWEq; auto using HUnionClamp, WUnionClamp.
  - apply YXEq; auto using YUnionClamp, XUnionClamp.
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
  intros g fuel; induction fuel as [| f IH]; intros y i.
  - now split. (* fuel = 0 *)
  - rewrite FilterFullLinesS; destruct (IsFullLineb g y). (* fuel = S n *)
    + apply IH.
    + now split.
Qed.

(* The lines of the filtered grid, at indices [i .. i + height), are exactly
 * non-full lines of g taken from [y .. y + fuel). Stated on [i] rather than on
 * [Y (result)]: in the recursive calls [i] runs ahead of [Y g], and the two
 * coincide only at the top-level call made by ClearFullLines. *)
Lemma FilterFullLinesSpec : ∀ (g : Grid) (fuel : ℕ) (y i : ℤ),
    0 ≤ H (FilterFullLines g fuel y i) ≤ Z.of_nat fuel
  ∧ (∀ j : ℤ,
       i ≤ j < i + H (FilterFullLines g fuel y i) →
       ∃ y' : ℤ,
           y ≤ y' < y + Z.of_nat fuel
         ∧ IsFullLineb g y' = false
         ∧ L (FilterFullLines g fuel y i) j = L g y').
Proof.
  intros g fuel; induction fuel as [| f IH]; intros y i.
  - (* No fuel: no line at all. *)
    assert (EH : H (FilterFullLines g 0 y i) = 0) by reflexivity.
    rewrite EH; split; (lia || intros j Hj; exfalso; lia).
  - (* Inductive case *)
    destruct (IsFullLineb g y) eqn: EF.
    + (* Line y is full: dropped; the result is the recursive one. *)
      assert (E : FilterFullLines g (S f) y i = FilterFullLines g f (y + 1) i)
        by (rewrite FilterFullLinesS, EF; reflexivity).
      rewrite E.
      destruct (IH (y + 1) i) as [Hbound Hrow]; split.
      * keep_only Hbound; lia.
      * intros j Hj; destruct (Hrow j Hj) as [y' (Hy' & HFb & HLrow)].
        exists y'; split.
        -- keep_only Hy'; lia.
        -- split; assumption.
    + (* Line y is kept, at index i; the lines above come from the recursion. *)
      assert (EH : H (FilterFullLines g (S f) y i)
                 = 1 + H (FilterFullLines g f (y + 1) (i + 1)))
        by (rewrite FilterFullLinesS, EF; reflexivity).
      assert (EL : ∀ j : ℤ,
                   L (FilterFullLines g (S f) y i) j
                   = if j =? i then L g y else L (FilterFullLines g f (y+1) (i+1)) j)
        by (intros j; rewrite FilterFullLinesS, EF; reflexivity).
      destruct (IH (y + 1) (i + 1)) as [Hbound Hrow].
      rewrite EH; split.
      * keep_only Hbound; lia.
      * intros j Hj; rewrite EL.
        destruct (Z.eq_dec j i) as [Ej | Ej].
        -- (* index i: line y of g, which is not full by EF *)
           exists y; rewrite Ej, Z.eqb_refl.
           split; (lia || split; (exact EF || reflexivity)).
        -- (* index above i: given by the induction hypothesis *)
           assert (Eb : (j =? i) = false) by (rewrite Z.eqb_neq; exact Ej).
           rewrite Eb.
           assert (Hj2 : i + 1 ≤ j < i + 1 + H (FilterFullLines g f (y+1) (i+1)))
             by lia.
           destruct (Hrow j Hj2) as [y' (Hy' & HFb & HLrow)].
           exists y'; split.
           ++ keep_only Hy'; lia.
           ++ split; (exact HFb || exact HLrow).
Qed.

Lemma ClearFullLinesBox : ∀ g : Grid,
  HW (ClearFullLines g) = HW g ∧ YX (ClearFullLines g) = YX g.
Proof.
  intros g.
  destruct (FilterFullLinesBox g (Z.to_nat (H g)) (Y g) (Y g)) as [EW EYX].
  assert (EHW : HW (ClearFullLines g)
              = (H g, W (FilterFullLines g (Z.to_nat (H g)) (Y g) (Y g))))
    by reflexivity.
  assert (EYX2 : YX (ClearFullLines g)
               = YX (FilterFullLines g (Z.to_nat (H g)) (Y g) (Y g)))
    by reflexivity.
  split.
  - rewrite EHW, EW; unfold H, W; symmetry; apply surjective_pairing.
  - rewrite EYX2; exact EYX.
Qed.

(* After clearing, no line is full: a kept line is a non-full line of g (same
 * row function, same X and W), and a line added on top is empty, hence not
 * full since the grid is at least one block wide. *)
Lemma ClearFullLinesNoFullLine : ∀ (g : Grid)
  (H1 : 0 ≤ H g)
  (H2 : 0 < W g),
  ¬ HasFullLine (ClearFullLines g).
Proof.
  intros g H1 H2 HF.
  remember (FilterFullLines g (Z.to_nat (H g)) (Y g) (Y g)) as g2 eqn: Eg2.
  assert (Em : ClearFullLines g = Resize g2 (H g) (λ _ : ℤ, false))
    by (rewrite Eg2; reflexivity).
  destruct (FilterFullLinesBox g (Z.to_nat (H g)) (Y g) (Y g)) as [EW2 EYX2].
  destruct (FilterFullLinesSpec g (Z.to_nat (H g)) (Y g) (Y g)) as [_ Hrow].
  rewrite <- Eg2 in EW2, EYX2, Hrow.
  assert (EY2 : Y g2 = Y g) by (unfold Y; rewrite EYX2; reflexivity).
  assert (EX2 : X g2 = X g) by (unfold X; rewrite EYX2; reflexivity).
  rewrite Em in HF; destruct HF as [j [Hj HFull]].
  set (m := Resize g2 (H g) (λ _ : ℤ, false)) in *.
  (* m has g's box, and its rows are those of g2 below Y g2 + H g2. *)
  assert (EYm : Y m = Y g2) by reflexivity.
  assert (EXm : X m = X g2) by reflexivity.
  assert (EWm : W m = W g2) by reflexivity.
  assert (EHm : H m = H g) by reflexivity.
  assert (ELm : ∀ y : ℤ,
                L m y = if y <? Y g2 + H g2 then L g2 y else (λ _ : ℤ, false))
    by reflexivity.
  rewrite EYm, EY2, EHm in Hj.
  destruct (j <? Y g2 + H g2) eqn: Ec.
  - (* j is a line copied from g *)
    rewrite Z.ltb_lt in Ec.
    assert (Erow : L m j = L g2 j) by (rewrite ELm; rewrite <- Z.ltb_lt in Ec;
                                       rewrite Ec; reflexivity).
    assert (Hjr : Y g ≤ j < Y g + H g2) by lia.
    destruct (Hrow j Hjr) as [y' (Hy' & HFb & HLrow)].
    apply (IsFullLinebFalseElim g y' HFb).
    intros x Hx.
    assert (Ex : L g y' x = L m j x) by (rewrite Erow, HLrow; reflexivity).
    rewrite Ex; apply HFull.
    rewrite EXm, EX2, EWm, EW2; exact Hx.
  - (* j is a line added on top, and it is empty *)
    rewrite Z.ltb_ge in Ec.
    assert (Erow : L m j = (λ _ : ℤ, false))
      by (rewrite ELm; rewrite <- Z.ltb_ge in Ec; rewrite Ec; reflexivity).
    assert (Efalse : L m j (X m) = false) by (rewrite Erow; reflexivity).
    assert (Etrue : L m j (X m) = true) by (apply HFull; rewrite EWm, EW2; lia).
    rewrite Efalse in Etrue; discriminate Etrue.
Qed.


(* ========================================================================= *)
(* Events: what they change, and the Valid they establish                     *)
(* ========================================================================= *)

Lemma MovePieceOK : ∀ dyx s s'
  (H1 : MovePiece dyx s = Some s'),
  let (dy, dx) := dyx in
    pyx s' = (py s + dy, px s + dx)
  ∧ mg s' = mg s
  ∧ p s' = p s
  ∧ pr s' = pr s
  ∧ gameover s' = gameover s.
Proof.
  intros; unfold MovePiece in H1.
  destruct (! gameover s && CanMovePiece dyx s); destruct dyx.
  - inject H1; now rewrite <- H1.
  - discriminate H1.
Qed.

(* Same, with dyx already destructed: avoids repeating [destruct dyx]. *)
Lemma MovePieceUnchanged : ∀ dyx s s'
  (H1 : MovePiece dyx s = Some s'),
    mg s' = mg s ∧ p s' = p s ∧ pr s' = pr s ∧ gameover s' = gameover s.
Proof.
  intros dyx s s' H1; apply MovePieceOK in H1; destruct dyx; tauto.
Qed.

Lemma CanMovePieceValid : ∀ (dy dx : ℤ) (s : State)
  (H1 : CanMovePiece (dy, dx) s = true),
  Valid (mg s) (p s) (py s + dy, px s + dx) (pr s) = true.
Proof.
  intros dy dx s H1.
  cbv beta iota zeta delta [CanMovePiece] in H1.
  apply andb_true_iff in H1; tauto.
Qed.

Lemma MovePieceValid : ∀ dyx s s'
  (H1 : MovePiece dyx s = Some s'),
  Valid (mg s') (p s') (pyx s') (pr s') = true.
Proof.
  intros dyx s s' H1; destruct dyx as [dy dx].
  cbv beta iota zeta delta [MovePiece] in H1.
  destruct (! gameover s && CanMovePiece (dy, dx) s) eqn: E; [ | discriminate H1 ].
  assert (Hc : CanMovePiece (dy, dx) s = true)
    (* by (apply (andb_true_iff (! gameover s) (CanMovePiece (dy, dx) s)) in E; tauto). *)
    by (apply andb_true_iff in E; tauto).
  assert (Hv : Valid (mg s) (p s) (py s + dy, px s + dx) (pr s) = true)
    by (apply CanMovePieceValid; exact Hc).
  inject H1; rewrite <- H1; exact Hv.
Qed.

Lemma RotatePieceOK : ∀ cw s s'
  (H1 : RotatePiece cw s = Some s'),
    mg s' = mg s
  ∧ p s' = p s
  ∧ pyx s' = pyx s
  ∧ gameover s' = gameover s
  ∧ pr s' = (pr s + (if cw then -1 else 1)) mod 4.
Proof.
  intros cw s s' H1; cbv beta iota zeta delta [RotatePiece] in H1.
  destruct (negb (gameover s)
            && Valid (mg s) (p s) (pyx s) ((pr s + (if cw then -1 else 1)) mod 4))
    eqn: E; [ | discriminate H1 ].
  inject H1; rewrite <- H1; repeat split.
Qed.

Lemma RotatePieceValid : ∀ cw s s'
  (H1 : RotatePiece cw s = Some s'),
  Valid (mg s') (p s') (pyx s') (pr s') = true.
Proof.
  intros cw s s' H1; cbv beta iota zeta delta [RotatePiece] in H1.
  destruct (negb (gameover s)
            && Valid (mg s) (p s) (pyx s) ((pr s + (if cw then -1 else 1)) mod 4))
    eqn: E; [ | discriminate H1 ].
  assert (Hv : Valid (mg s) (p s) (pyx s)
                     ((pr s + (if cw then -1 else 1)) mod 4) = true)
    by (apply andb_true_iff in E; tauto).
  inject H1; rewrite <- H1; exact Hv.
Qed.

Lemma FixPieceOK : ∀ pNew s s'
  (H1 : FixPiece pNew s = Some s'),
    mg s' = ClearFullLines ((mg s ∪ (PieceGrid s ⊕ pyx s)) ∩ Full (mg s))
  ∧ p s' = pNew
  ∧ pyx s' = InitialYX pNew
  ∧ pr s' = 0
  ∧ gameover s' = (ForbiddenGrid ∩ mg s' ⊈ ∅).
Proof.
  intros pNew s s' H1; cbv beta iota zeta delta [FixPiece] in H1.
  destruct (! gameover s && ! CanMovePiece (-1, 0) s) eqn: E; [ | discriminate H1 ].
  inject H1; rewrite <- H1; repeat split.
Qed.

(* The two piece invariants are precisely the two conjuncts of Valid. *)
Lemma ValidPieceInvariants : ∀ s : State,
  Valid (mg s) (p s) (pyx s) (pr s) = true →
  PieceOccupiedInsideBounds s ∧ PieceOnFreeBlocks s.
Proof.
  intros s HV; cbv beta zeta delta [Valid] in HV.
  apply andb_true_iff in HV as [HV1 HV2].
  unfold PieceOccupiedInsideBounds, PieceOnFreeBlocks, PieceGrid.
  split; (exact HV1 || intros _; exact HV2).
Qed.

Definition NewPieceGrid (p : Piece) : Grid :=
  RotGrid p 0 ⊕ InitialYX p.

(* A newly chosen piece appears in the forbidden zone, hence inside any grid
 * having the main grid's box, and on free blocks as long as the forbidden zone
 * is free, i.e. as long as the game is not over. *)
Lemma NewPieceInsideBounds : ∀ (pNew : Piece) (g : Grid)
  (EHW : HW g = HW InitialMainGrid)
  (EYX : YX g = YX InitialMainGrid),
  NewPieceGrid pNew ⊆ Full g = true.
Proof.
  intros pNew g EHW EYX.
  assert (EF : Full g = Full InitialMainGrid) by (apply FullBoxEq; assumption).
  rewrite EF.
  assert (L1 : NewPieceGrid pNew ⊆ ForbiddenGrid = true)
    by (destruct (AxiomsRotGrid pNew) as [_ L]; exact L).
  assert (L2 : ForbiddenGrid ⊆ Full InitialMainGrid = true). {
    assert (L2_1 : Full ForbiddenGrid ⊆ Full InitialMainGrid = true)
      by (destruct AxiomsForbiddenGrid as (_ & _ & _ & L); exact L).
    keep_only L2_1; now apply GridIncludeFullImpliesNonFull.
  }
  eapp GridIncludeTransitive.
Qed.

Lemma NewPieceFree : ∀ (pNew : Piece) (g : Grid)
  (H1 : ForbiddenGrid ∩ g ⊆ ∅ = true),
  NewPieceGrid pNew ∩ g ⊆ ∅ = true.
Proof.
  intros pNew g H1.
  assert (L1 : NewPieceGrid pNew ⊆ ForbiddenGrid = true)
    by (destruct (AxiomsRotGrid pNew) as [_ L]; exact L).
  assert (L2 : NewPieceGrid pNew ∩ g ⊆ ForbiddenGrid ∩ g = true)
    by (apply GridIntersectMonotoneLeft; exact L1).
  eapp GridIncludeTransitive.
Qed.


(* ========================================================================= *)
(* SpecCorrect (safety)                                                      *)
(* ========================================================================= *)

(***************)
(* InitCorrect *)
(***************)

Lemma InitTypeOK : ∀ p : Piece, TypeOK (Init p).
Proof.
  intros; unfold TypeOK, Init; split_top; now simpl.
Qed.

Lemma InitGameover : ∀ p : Piece, Gameover (Init p).
Proof.
  intros; unfold Gameover, Init; now simpl.
Qed.

Lemma InitPieceOccupiedInsideBounds : ∀ p : Piece, PieceOccupiedInsideBounds (Init p).
Proof.
  intros p.
  assert (Egp : PieceGrid (Init p) ⊕ pyx (Init p) = NewPieceGrid p) by reflexivity.
  assert (Emg : mg (Init p) = InitialMainGrid) by reflexivity.
  unfold PieceOccupiedInsideBounds; rewrite Egp, Emg.
  apply NewPieceInsideBounds; reflexivity.
Qed.

Lemma InitPieceOnFreeBlocks : ∀ p : Piece, PieceOnFreeBlocks (Init p).
Proof.
  intros p; unfold PieceOnFreeBlocks; intros HGo.
  assert (Egp : PieceGrid (Init p) ⊕ pyx (Init p) = NewPieceGrid p) by reflexivity.
  assert (Emg : mg (Init p) = InitialMainGrid) by reflexivity.
  assert (Ego : gameover (Init p) = (ForbiddenGrid ∩ InitialMainGrid ⊈ ∅))
    by reflexivity.
  assert (L1 : ForbiddenGrid ∩ InitialMainGrid ⊆ ∅ = true). {
    rewrite Ego in HGo; keep_only HGo.
    destruct (ForbiddenGrid ∩ InitialMainGrid ⊆ ∅); [ reflexivity | discriminate HGo ].
  }
  rewrite Egp, Emg; exact (NewPieceFree p InitialMainGrid L1).
Qed.

Lemma InitNoFullLine : ∀ p : Piece, NoFullLine (Init p).
Proof.
  intros p.
  assert (L1 : YX InitialMainGrid = (0, 0))
    by now destruct AxiomsInitialMainGrid; tauto.
  assert (L2 : ∀ y : ℤ, 0 ≤ y < H InitialMainGrid → ¬ IsFullLine InitialMainGrid y)
    by now destruct AxiomsInitialMainGrid; tauto.
  assert (EY : Y InitialMainGrid = 0) by (unfold Y; now rewrite L1).
  assert (Emg : mg (Init p) = InitialMainGrid) by reflexivity.
  unfold NoFullLine; rewrite Emg.
  intros [y [Hy HFull]].
  apply (L2 y); [ keep_only Hy EY; lia | exact HFull ].
Qed.

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

Lemma TypeOKSpec : ∀ s,
  TypeOK s ↔ (
      HW (mg s) = HW InitialMainGrid
    ∧ YX (mg s) = YX InitialMainGrid
    ∧ 0 ≤ pr s ≤ 3
  ).
Proof. reflexivity. Qed.

Lemma TypeOKSpec2 : ∀ s,
  TypeOK s → (
      HW (mg s) = HW InitialMainGrid
    ∧ YX (mg s) = YX InitialMainGrid
    ∧ 0 ≤ pr s ≤ 3
  ).
Proof. intros. destruct (TypeOKSpec s); tauto. Qed.

Lemma InitCorrect : ∀ p : Piece, Correct (Init p).
Proof.
  intros.
  apply CorrectSpec; split_top; auto using InitTypeOK, InitGameover,
    InitPieceOccupiedInsideBounds, InitPieceOnFreeBlocks, InitNoFullLine.
Qed.

(***************)
(* NextCorrect *)
(***************)

(**** MovePieceCorrect ****)

Lemma MovePieceTypeOK : ∀ s s' dyx
  (H1 : Correct s)
  (H2 : MovePiece dyx s = Some s'),
  TypeOK s'.
Proof.
  intros.
  (* TypeOK uses only `mg s` and `pr s` and both are unchanged. *)
  assert (L1 : mg s' = mg s)
    by now apply MovePieceOK in H2; destruct dyx in H2; tauto.
  assert (L2 : pr s' = pr s)
    by now apply MovePieceOK in H2; destruct dyx in H2; tauto.
  apply CorrectSpec in H1.
  unfold TypeOK in *; split_top;
    keep_only H1 L1 L2; try ((rewrite L1; tauto) || (rewrite L2; lia)).
Qed.

Lemma MovePieceGameover : ∀ [s s' dyx]
  (H1 : Correct s)
  (H2 : MovePiece dyx s = Some s'),
  Gameover s'.
Proof.
  intros.
  set (M := MovePieceUnchanged dyx s s' H2).
  assert (L1 : mg s' = mg s) by now destruct M; tauto.
  assert (L2 : gameover s' = gameover s) by now destruct M; tauto.
  assert (L3 : Gameover s) by now destruct H1; tauto.
  unfold Gameover in *.
  rewrite L1, L2; exact L3.
Qed.

Lemma MovePiecePieceOccupiedInsideBounds : ∀ s s' dyx
  (H1 : Correct s)
  (H2 : MovePiece dyx s = Some s'),
  PieceOccupiedInsideBounds s'.
Proof.
  intros.
  assert (L1 : Valid (mg s') (p s') (pyx s') (pr s') = true) by (eapp MovePieceValid).
  keep_only L1; destruct (ValidPieceInvariants s' L1) as [L2 _]; exact L2.
Qed.

Lemma MovePiecePieceOnFreeBlocks : ∀ s s' dyx
  (H1 : Correct s)
  (H2 : MovePiece dyx s = Some s'),
  PieceOnFreeBlocks s'.
Proof.
  intros.
  assert (L1 : Valid (mg s') (p s') (pyx s') (pr s') = true) by (eapp MovePieceValid).
  keep_only L1; destruct (ValidPieceInvariants s' L1) as [_ L2]; exact L2.
Qed.

Lemma MovePieceNoFullLine : ∀ s s' dyx
  (H1 : Correct s)
  (H2 : MovePiece dyx s = Some s'),
  NoFullLine s'.
Proof.
  intros.
  set (M := MovePieceUnchanged dyx s s' H2).
  assert (L1 : mg s' = mg s) by now destruct M; tauto.
  assert (L2 : NoFullLine s) by now apply CorrectSpec in H1; tauto.
  keep_only L1 L2; unfold NoFullLine in *; rewrite L1; exact L2.
Qed.

(* CorrectWithoutGameover-only counterparts: preserved given only
CorrectWithoutGameover held before, with no need for the bidirectional
Gameover fact (confirmed by inspection, none of MovePieceTypeOK/
PieceOccupiedInsideBounds/PieceOnFreeBlocks/NoFullLine above actually use the
Gameover component of Correct, only CorrectWithoutGameover's own parts). *)
Lemma MovePieceCorrectWithoutGameover : ∀ [s s' dyx]
  (H1 : CorrectWithoutGameover s)
  (H2 : MovePiece dyx s = Some s'),
  CorrectWithoutGameover s'.
Proof.
  intros.
  assert (L1 : mg s' = mg s ∧ pr s' = pr s)
    by (apply MovePieceOK in H2; destruct dyx in H2; tauto).
  unfold CorrectWithoutGameover in H1; destruct H1 as (H1a & H1b & H1c & H1d).
  destruct L1 as [L1a L1b].
  assert (L2 : Valid (mg s') (p s') (pyx s') (pr s') = true) by (eapp MovePieceValid).
  destruct (ValidPieceInvariants s' L2) as [L3 L4].
  unfold CorrectWithoutGameover; split; [ | split; [ | split]].
  - unfold TypeOK in *; rewrite L1a, L1b; exact H1a.
  - exact L3.
  - exact L4.
  - unfold NoFullLine in *; rewrite L1a; exact H1d.
Qed.

Lemma MovePieceCorrect : ∀ [s s' dyx]
  (H1 : Correct s)
  (H2 : MovePiece dyx s = Some s'),
  Correct s'.
Proof.
  intros; unfold Correct in *; split.
  - apply (MovePieceCorrectWithoutGameover (proj1 H1) H2).
  - apply (MovePieceGameover H1 H2).
Qed.

(* Only PieceOnFreeBlocks needs anything gameover-related, and only its weak
direction: not-gameover plus (forbidden-intersect implies gameover) is enough
to know the forbidden zone (hence, via AxiomsRotGrid, the fresh piece) is
clear of existing blocks (the full biconditional Gameover is never used). *)
Lemma NewPieceStateCorrectWithoutGameover : ∀ (pNew : Piece) (s : State)
  (H1 : CorrectWithoutGameover s)
  (H2 : ForbiddenGrid ∩ mg s ⊈ ∅ = true → gameover s = true),
  CorrectWithoutGameover (NewPieceState pNew s).
Proof.
  intros.
  unfold CorrectWithoutGameover in H1; destruct H1 as (HT & _ & _ & HN).
  assert (EHW : HW (mg s) = HW InitialMainGrid) by now apply TypeOKSpec2 in HT; tauto.
  assert (EYX : YX (mg s) = YX InitialMainGrid) by now apply TypeOKSpec2 in HT; tauto.
  assert (Emg : mg (NewPieceState pNew s) = mg s) by reflexivity.
  assert (Ego : gameover (NewPieceState pNew s) = gameover s) by reflexivity.
  assert (Epr : pr (NewPieceState pNew s) = 0) by reflexivity.
  assert (Egp : PieceGrid (NewPieceState pNew s) ⊕ pyx (NewPieceState pNew s)
              = NewPieceGrid pNew) by reflexivity.
  assert (L1 : TypeOK (NewPieceState pNew s)). {
    unfold TypeOK. split_top;
      (rewrite Emg; exact EHW) || (rewrite Emg; exact EYX) || (rewrite Epr; lia).
  }
  assert (L2 : PieceOccupiedInsideBounds (NewPieceState pNew s)). {
    unfold PieceOccupiedInsideBounds; rewrite Egp, Emg.
    apply NewPieceInsideBounds; assumption.
  }
  assert (L3 : PieceOnFreeBlocks (NewPieceState pNew s)). {
    unfold PieceOnFreeBlocks; intros HGo; rewrite Egp, Emg.
    apply NewPieceFree.
    rewrite Ego in HGo.
    destruct (ForbiddenGrid ∩ mg s ⊆ ∅) eqn: E; [ reflexivity | exfalso ].
    assert (L3' : ForbiddenGrid ∩ mg s ⊈ ∅ = true) by (rewrite E; reflexivity).
    rewrite (H2 eq_refl) in HGo; discriminate HGo.
  }
  assert (L4 : NoFullLine (NewPieceState pNew s))
    by (unfold NoFullLine in *; rewrite Emg; exact HN).
  unfold CorrectWithoutGameover; split; [ | split; [ | split]]; assumption.
Qed.


Lemma RotatePieceTypeOK : ∀ s s' cw
  (H1 : Correct s)
  (H2 : RotatePiece cw s = Some s'),
  TypeOK s'.
Proof.
  intros.
  pose proof (RotatePieceOK cw s s' H2) as L1.
  apply CorrectSpec in H1. unfold TypeOK in H1.
  assert (L2 : HW (mg s) = HW InitialMainGrid) by now keep_only H1; tauto.
  assert (L3 : YX (mg s) = YX InitialMainGrid) by now keep_only H1; tauto.
  assert (L4 : mg s' = mg s) by now keep_only L1; tauto.
  assert (L5 : pr s' = (pr s + (if cw then -1 else 1)) mod 4)
    by now keep_only L1; tauto.
  assert (L6 : 0 ≤ (pr s + (if cw then -1 else 1)) mod 4 < 4)
    by (apply Z.mod_pos_bound; lia).
  keep_only L2 L3 L4 L5 L6.
  apply TypeOKSpec; repeat split; (rewrite L4 || rewrite L5); (assumption || lia).
Qed.

Lemma RotatePieceGameover : ∀ [s s' cw]
  (H1 : Correct s)
  (H2 : RotatePiece cw s = Some s'),
  Gameover s'.
Proof.
  intros.
  set (R := RotatePieceOK cw s s' H2).
  assert (L1 : mg s' = mg s) by now destruct R; tauto.
  assert (L2 : gameover s' = gameover s) by now destruct R; tauto.
  assert (L3 : Gameover s) by now apply CorrectSpec in H1; tauto.
  keep_only L1 L2 L3. unfold Gameover in *; rewrite L1, L2; exact L3.
Qed.

Lemma RotatePiecePieceOccupiedInsideBounds : ∀ s s' cw
  (H1 : Correct s)
  (H2 : RotatePiece cw s = Some s'),
  PieceOccupiedInsideBounds s'.
Proof.
  intros.
  assert (L1 : Valid (mg s') (p s') (pyx s') (pr s') = true) by (eapp RotatePieceValid).
  keep_only L1; destruct (ValidPieceInvariants s' L1) as [L2 _]; exact L2.
Qed.

Lemma RotatePiecePieceOnFreeBlocks : ∀ s s' cw
  (H1 : Correct s)
  (H2 : RotatePiece cw s = Some s'),
  PieceOnFreeBlocks s'.
Proof.
  intros.
  assert (L1 : Valid (mg s') (p s') (pyx s') (pr s') = true) by (eapp RotatePieceValid).
  keep_only L1; destruct (ValidPieceInvariants s' L1) as [_ L2]; exact L2.
Qed.

Lemma RotatePieceNoFullLine : ∀ s s' cw
  (H1 : Correct s)
  (H2 : RotatePiece cw s = Some s'),
  NoFullLine s'.
Proof.
  intros.
  set (R := RotatePieceOK cw s s' H2).
  assert (L1 : mg s' = mg s) by now destruct R; tauto.
  assert (L2 : NoFullLine s) by now apply CorrectSpec in H1; tauto.
  keep_only L1 L2; unfold NoFullLine in *; rewrite L1; exact L2.
Qed.

Lemma RotatePieceCorrectWithoutGameover : ∀ [s s' cw]
  (H1 : CorrectWithoutGameover s)
  (H2 : RotatePiece cw s = Some s'),
  CorrectWithoutGameover s'.
Proof.
  intros.
  pose proof (RotatePieceOK cw s s' H2) as L1.
  unfold CorrectWithoutGameover in H1; destruct H1 as (H1a & H1b & H1c & H1d).
  assert (L2 : HW (mg s) = HW InitialMainGrid)
    by now keep_only H1a; unfold TypeOK in H1a; tauto.
  assert (L3 : YX (mg s) = YX InitialMainGrid)
    by now keep_only H1a; unfold TypeOK in H1a; tauto.
  assert (L4 : mg s' = mg s) by now keep_only L1; tauto.
  assert (L5 : pr s' = (pr s + (if cw then -1 else 1)) mod 4)
    by now keep_only L1; tauto.
  assert (L6 : 0 ≤ (pr s + (if cw then -1 else 1)) mod 4 < 4)
    by (apply Z.mod_pos_bound; lia).
  assert (L7 : TypeOK s')
    by (apply TypeOKSpec; repeat split; (rewrite L4 || rewrite L5); (assumption || lia)).
  assert (L8 : Valid (mg s') (p s') (pyx s') (pr s') = true) by (eapp RotatePieceValid).
  destruct (ValidPieceInvariants s' L8) as [L9 L10].
  unfold CorrectWithoutGameover; split; [ | split; [ | split]].
  - exact L7.
  - exact L9.
  - exact L10.
  - unfold NoFullLine in *; rewrite L4; exact H1d.
Qed.

Lemma RotatePieceCorrect : ∀ [s s' dyx]
  (H1 : Correct s)
  (H2 : RotatePiece dyx s = Some s'),
  Correct s'.
Proof.
  intros; unfold Correct in *; split.
  - apply (RotatePieceCorrectWithoutGameover (proj1 H1) H2).
  - apply (RotatePieceGameover H1 H2).
Qed.


(**** FixPieceCorrect ****)

Lemma FixPieceTypeOK : ∀ s s' pNew
  (H1 : Correct s)
  (H2 : FixPiece pNew s = Some s'),
  TypeOK s'.
Proof.
  intros.
  set (F := FixPieceOK pNew s s' H2).
  assert (L1 : mg s' = ClearFullLines ((mg s ∪ PieceGrid s ⊕ pyx s) ∩ Full (mg s)))
    by now destruct F; tauto.
  assert (L2 : pr s' = 0) by now destruct F; tauto.
  assert (L3 : TypeOK s) by now apply CorrectSpec in H1; tauto.
  assert (L4 : HW (mg s) = HW InitialMainGrid ∧ YX (mg s) = YX InitialMainGrid)
    by now apply TypeOKSpec2 in L3; tauto.
  destruct (ClearFullLinesBox ((mg s ∪ (PieceGrid s ⊕ pyx s)) ∩ Full (mg s)))
    as [C1 C2].
  destruct (BoxUnionClamp (mg s) (PieceGrid s ⊕ pyx s)) as [B1 B2].
  unfold TypeOK; split_top;
    ((rewrite L1, C1, B1 || rewrite L1, C2, B2); (keep_only L4; tauto)) ||
    rewrite L2; lia.
Qed.

Lemma FixPieceGameover : ∀ [s s' pNew]
  (H1 : Correct s)
  (H2 : FixPiece pNew s = Some s'),
  Gameover s'.
Proof.
  intros.
  (* gameover s' is *defined* as the forbidden zone meeting the new main grid. *)
  destruct (FixPieceOK pNew s s' H2) as (_ & _ & _ & _ & Ego).
  keep_only Ego; unfold Gameover; rewrite Ego; tauto.
Qed.

Lemma FixPiecePieceOccupiedInsideBounds : ∀ s s' pNew
  (H1 : Correct s)
  (H2 : FixPiece pNew s = Some s'),
  PieceOccupiedInsideBounds s'.
Proof.
  intros.
  destruct (FixPieceOK pNew s s' H2) as (_ & Ep & Epyx & Epr & _).
  assert (LT : TypeOK s') by (eapp FixPieceTypeOK).
  destruct LT as (EHW & EYX & _).
  unfold PieceOccupiedInsideBounds, PieceGrid; rewrite Ep, Epr, Epyx.
  change (NewPieceGrid pNew ⊆ Full (mg s') = true).
  apply NewPieceInsideBounds; assumption.
Qed.

Lemma FixPiecePieceOnFreeBlocks : ∀ s s' pNew
  (H1 : Correct s)
  (H2 : FixPiece pNew s = Some s'),
  PieceOnFreeBlocks s'.
Proof.
  intros.
  destruct (FixPieceOK pNew s s' H2) as (_ & Ep & Epyx & Epr & Ego).
  unfold PieceOnFreeBlocks, PieceGrid; intros HGo; rewrite Ep, Epr, Epyx.
  change (NewPieceGrid pNew ∩ mg s' ⊆ ∅ = true).
  assert (L1 : ForbiddenGrid ∩ mg s' ⊆ ∅ = true). {
    rewrite Ego in HGo; keep_only HGo.
    destruct (ForbiddenGrid ∩ mg s' ⊆ ∅); [ reflexivity | discriminate HGo ].
  }
  exact (NewPieceFree pNew (mg s') L1).
Qed.

Lemma FixPieceNoFullLine : ∀ s s' pNew
  (H1 : Correct s)
  (H2 : FixPiece pNew s = Some s'),
  NoFullLine s'.
Proof.
  intros.
  assert (L1 : mg s' = ClearFullLines ((mg s ∪ PieceGrid s ⊕ pyx s) ∩ Full (mg s)))
    by now destruct (FixPieceOK pNew s s' H2); tauto.
  assert (L2 : HW (mg s) = HW InitialMainGrid). {
    assert (L2_1 : TypeOK s) by now apply CorrectSpec in H1; tauto.
    apply TypeOKSpec2 in L2_1; tauto.
  }
  assert (L3 : H (mg s) = H InitialMainGrid) by (unfold H; now rewrite L2).
  assert (L4 : W (mg s) = W InitialMainGrid) by (unfold W; now rewrite L2).
  assert (L5 : H InitialMainGrid > 0) by now destruct AxiomsInitialMainGrid; tauto.
  assert (L6 : W InitialMainGrid > 0) by now destruct AxiomsInitialMainGrid; tauto.
  unfold NoFullLine; rewrite L1.
  apply ClearFullLinesNoFullLine;
   (rewrite HUnionClamp, L3; keep_only L5) ||
   (rewrite WUnionClamp, L4; keep_only L6); lia.
Qed.

Lemma FixPieceCorrectWithoutGameover : ∀ [s s' pNew]
  (H1 : CorrectWithoutGameover s)
  (H2 : FixPiece pNew s = Some s'),
  CorrectWithoutGameover s'.
Proof.
  intros.
  set (F := FixPieceOK pNew s s' H2).
  unfold CorrectWithoutGameover in H1; destruct H1 as (H1a & H1b & H1c & H1d).
  assert (L1 : mg s' = ClearFullLines ((mg s ∪ PieceGrid s ⊕ pyx s) ∩ Full (mg s)))
    by now destruct F; tauto.
  assert (L2 : pr s' = 0) by now destruct F; tauto.
  assert (L4 : HW (mg s) = HW InitialMainGrid ∧ YX (mg s) = YX InitialMainGrid)
    by now apply TypeOKSpec2 in H1a; tauto.
  assert (L5 : TypeOK s'). {
    destruct (ClearFullLinesBox ((mg s ∪ (PieceGrid s ⊕ pyx s)) ∩ Full (mg s))) as [C1 C2].
    destruct (BoxUnionClamp (mg s) (PieceGrid s ⊕ pyx s)) as [B1 B2].
    unfold TypeOK; split_top;
      ((rewrite L1, C1, B1 || rewrite L1, C2, B2); (keep_only L4; tauto)) ||
      rewrite L2; lia.
  }
  assert (L6 : PieceOccupiedInsideBounds s'). {
    destruct L5 as (EHW & EYX & _).
    destruct F as (_ & Ep & Epyx & Epr & _).
    unfold PieceOccupiedInsideBounds, PieceGrid; rewrite Ep, Epr, Epyx.
    change (NewPieceGrid pNew ⊆ Full (mg s') = true).
    apply NewPieceInsideBounds; assumption.
  }
  assert (L7 : PieceOnFreeBlocks s'). {
    destruct F as (_ & Ep & Epyx & Epr & Ego).
    unfold PieceOnFreeBlocks, PieceGrid; intros HGo; rewrite Ep, Epr, Epyx.
    change (NewPieceGrid pNew ∩ mg s' ⊆ ∅ = true).
    assert (L8 : ForbiddenGrid ∩ mg s' ⊆ ∅ = true). {
      rewrite Ego in HGo; keep_only HGo.
      destruct (ForbiddenGrid ∩ mg s' ⊆ ∅); [ reflexivity | discriminate HGo ].
    }
    exact (NewPieceFree pNew (mg s') L8).
  }
  assert (L9 : NoFullLine s'). {
    assert (L10 : H (mg s) = H InitialMainGrid) by (unfold H; now rewrite (proj1 L4)).
    assert (L11 : W (mg s) = W InitialMainGrid) by now unfold W; now rewrite (proj1 L4).
    assert (L12 : H InitialMainGrid > 0) by now destruct AxiomsInitialMainGrid; tauto.
    assert (L13 : W InitialMainGrid > 0) by now destruct AxiomsInitialMainGrid; tauto.
    unfold NoFullLine; rewrite L1.
    apply ClearFullLinesNoFullLine;
      (rewrite HUnionClamp, L10; keep_only L12) ||
      (rewrite WUnionClamp, L11; keep_only L13); lia.
  }
  unfold CorrectWithoutGameover; split; [ | split; [ | split]]; assumption.
Qed.

Lemma FixPieceCorrect : ∀ s s' pNew
  (H1 : Correct s)
  (H2 : FixPiece pNew s = Some s'),
  Correct s'.
Proof.
  intros; unfold Correct in *; split.
  - apply (FixPieceCorrectWithoutGameover (proj1 H1) H2).
  - apply (FixPieceGameover H1 H2).
Qed.


(**** FallStepCorrect ****)

(* A fall step is a move down, or a fix. Nothing to prove per invariant. *)
Lemma FallStepCorrect : ∀ s s' pNew
  (H1 : Correct s)
  (H2 : FallStep pNew s = Some s'),
  Correct s'.
Proof.
  intros; unfold FallStep in H2.
  destruct (MovePiece (-1, 0) s) as [s2 |] eqn: E.
  - assert (L1 : s2 = s') by (inject H2; exact H2).
    rewrite L1 in E; eapp MovePieceCorrect.
  - eapp FixPieceCorrect.
Qed.


(**** StutterCorrect ****)

Lemma StutterCorrect : ∀ s s'
  (H1 : Correct s)
  (H2 : Next Stutter s = Some s'),
  Correct s'.
Proof.
  intros; unfold Correct; split_top; sauto.
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
  intros.
  destruct (MovePiece (-1, 0) s) as [s2| ] eqn: H2.
  - Check (H2 : MovePiece (-1, 0) s = Some s2).
    exists s2.
    unfold FallStep; now rewrite H2.
  - Check (H2 : MovePiece (-1, 0) s = None).
    enough (∃ s', FixPiece pNew s = Some s')
      by now unfold FallStep; rewrite H2.
    assert (L1 : CanMovePiece (-1, 0) s = false). {
      unfold MovePiece in H2.
      rewrite H1 in H2.
      destruct (CanMovePiece (-1, 0) s) eqn: H3 in H2.
      - discriminate H2.
      - exact H3. 
    }
    unfold FixPiece. rewrite H1, L1. simpl.
    now eexists.
Qed.

(* ========================================================================= *)
(* Helpers for refining models                                               *)
(* ========================================================================= *)

(* Choosing a new current piece preserves Correct. This is the T1 content of any
 * higher-level event that spawns a piece without touching the main grid — T3's
 * HoldPiece, and later T4's preview pop. The two non-trivial conjuncts are
 * exactly NewPieceInsideBounds and NewPieceFree, already isolated above for Init
 * and FixPiece. *)
Lemma NewPieceStateCorrect : ∀ (pNew : Piece) (s : State)
  (H1 : Correct s),
  Correct (NewPieceState pNew s).
Proof.
  intros pNew s H1.
  assert (HT : TypeOK s) by now apply CorrectSpec in H1; tauto.
  assert (HN : NoFullLine s) by now apply CorrectSpec in H1; tauto.
  assert (HG : Gameover s) by now apply CorrectSpec in H1; tauto.
  assert (EHW : HW (mg s) = HW InitialMainGrid) by now apply TypeOKSpec2 in HT; tauto.
  assert (EYX : YX (mg s) = YX InitialMainGrid) by now apply TypeOKSpec2 in HT; tauto.
  (* Only p, pyx and pr change; mg, gameover and clearedLines are carried over. *)
  assert (Emg : mg (NewPieceState pNew s) = mg s) by reflexivity.
  assert (Ego : gameover (NewPieceState pNew s) = gameover s) by reflexivity.
  assert (Epr : pr (NewPieceState pNew s) = 0) by reflexivity.
  assert (Egp : PieceGrid (NewPieceState pNew s) ⊕ pyx (NewPieceState pNew s)
              = NewPieceGrid pNew) by reflexivity.
  assert (L1 : TypeOK (NewPieceState pNew s)). {
    (* TypeOK: the box is the one of `mg s`, and the new rotation is 0. *)
    unfold TypeOK. split_top;
      (rewrite Emg; exact EHW) || (rewrite Emg; exact EYX) || (rewrite Epr; lia).
  }
  assert (L2 : PieceOccupiedInsideBounds (NewPieceState pNew s)). {
    (* The new piece appears inside the forbidden zone, itself inside mg's box. *)
    unfold PieceOccupiedInsideBounds; rewrite Egp, Emg.
    apply NewPieceInsideBounds; assumption.
  }
  assert (L3 : PieceOnFreeBlocks (NewPieceState pNew s)). {
    (* Not being gameover means the forbidden zone is free of occupied blocks,
     * hence so is the new piece, which is included in it. *)
    unfold PieceOnFreeBlocks; intros HGo; rewrite Egp, Emg.
    apply NewPieceFree.
    rewrite Ego in HGo.
    unfold Gameover in HG; destruct HG as [_ HG2].
    destruct (ForbiddenGrid ∩ mg s ⊆ ∅) eqn: E; [ reflexivity | exfalso ].
    rewrite (HG2 eq_refl) in HGo; discriminate HGo.
  }
  assert (L4 : NoFullLine (NewPieceState pNew s)). {
    (* NoFullLine: `mg` is unchanged. *)
    unfold NoFullLine in *; rewrite Emg; exact HN.
  }
  assert (L5 : Gameover (NewPieceState pNew s)). {
    (* Gameover: neither `mg` nor `gameover` changed. *)
    unfold Gameover in *; rewrite Emg, Ego; exact HG.
  }
  apply CorrectSpec; split_top; auto using L1, L2, L3, L4, L5.
Qed.

(* Relocating the current piece (same p, same pr) preserves Correct, given the
 * target position is already Valid. Simpler than NewPieceStateCorrect: it
 * doesn't need ForbiddenGrid reasoning at all, since ValidPieceInvariants
 * already is the pair of invariants NewPieceYXState needs. Used by T5's
 * DropPiece, whose target position is exactly the one LowestShadowY certifies
 * as Valid. *)
Lemma NewPieceYXStateCorrect : ∀ (pyxNew : ℤ × ℤ) (s : State)
  (H1 : Correct s)
  (H2 : Valid (mg s) (p s) pyxNew (pr s) = true),
  Correct (NewPieceYXState pyxNew s).
Proof.
  intros pyxNew s H1 H2.
  assert (Hc : TypeOK s ∧ PieceOccupiedInsideBounds s ∧ PieceOnFreeBlocks s ∧
               NoFullLine s ∧ Gameover s) by now apply CorrectSpec in H1 as Hc.
  assert (Emg : mg (NewPieceYXState pyxNew s) = mg s) by reflexivity.
  assert (Ego : gameover (NewPieceYXState pyxNew s) = gameover s) by reflexivity.
  assert (Epr : pr (NewPieceYXState pyxNew s) = pr s) by reflexivity.
  assert (Ep : p (NewPieceYXState pyxNew s) = p s) by reflexivity.
  assert (Epyx : pyx (NewPieceYXState pyxNew s) = pyxNew) by reflexivity.
  assert (H2' : Valid (mg (NewPieceYXState pyxNew s)) (p (NewPieceYXState pyxNew s))
                      (pyx (NewPieceYXState pyxNew s)) (pr (NewPieceYXState pyxNew s)) = true)
    by (rewrite Emg, Ep, Epyx, Epr; exact H2).
  unfold TypeOK in Hc.
  keep_only Hc Emg Ego Epr H2'.
  assert (L1 : TypeOK (NewPieceYXState pyxNew s))
    by now apply TypeOKSpec; split_top; (rewrite Emg; tauto) || (rewrite Epr; lia).
  assert (L2 : PieceOccupiedInsideBounds (NewPieceYXState pyxNew s))
    by now destruct (ValidPieceInvariants (NewPieceYXState pyxNew s) H2').
  assert (L3 : PieceOnFreeBlocks (NewPieceYXState pyxNew s))
    by now destruct (ValidPieceInvariants (NewPieceYXState pyxNew s) H2').
  assert (L4 : NoFullLine (NewPieceYXState pyxNew s))
    by now unfold NoFullLine in *; rewrite Emg; keep_only Hc; tauto.
  assert (L5 : Gameover (NewPieceYXState pyxNew s))
    by now unfold Gameover in *; rewrite Emg, Ego; keep_only Hc; tauto.
  apply CorrectSpec; split_top; auto using L1, L2, L3, L4, L5.
Qed.

(* A state satisfying Correct, when not gameover, has its current piece Valid —
 * PieceOccupiedInsideBounds and PieceOnFreeBlocks (the latter needs the
 * hypothesis) are exactly Valid's two conjuncts. *)
Lemma CorrectImpliesValid : ∀ (s : State)
  (H1 : Correct s)
  (H2 : gameover s = false),
  Valid (mg s) (p s) (pyx s) (pr s) = true.
Proof.
  intros s H1 H2.
  assert (L1 : PieceOccupiedInsideBounds s) by now apply CorrectSpec in H1; tauto.
  assert (L2 : PieceOnFreeBlocks s) by now apply CorrectSpec in H1; tauto.
  unfold Valid, PieceGrid in *.
  apply andb_true_iff; split; (exact L1 || exact (L2 H2)).
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
  intros g pc py px pr HY HR HP.
  destruct (Valid g pc (py, px) pr) eqn: E; [ exfalso | reflexivity ].
  unfold Valid in E; apply andb_true_iff in E as [E1 _].
  destruct (AxiomsRotGrid pc) as [HAll _].
  destruct (HAll pr HR) as (EHW & EYX & _ & (ry & rx & Hry & Hrx & HL)).
  assert (EHrg : H (RotGrid pc pr) = PW) by (unfold H; rewrite EHW; reflexivity).
  assert (EYrg : Y (RotGrid pc pr) = 0) by (unfold Y; rewrite EYX; reflexivity).
  assert (EXrg : X (RotGrid pc pr) = 0) by (unfold X; rewrite EYX; reflexivity).
  assert (EWrg : W (RotGrid pc pr) = PW) by (unfold W; rewrite EHW; reflexivity).
  assert (EYgp : Y (RotGrid pc pr ⊕ (py, px)) = py)
    by (assert (E0 : Y (RotGrid pc pr ⊕ (py, px)) = Y (RotGrid pc pr) + py) by reflexivity;
        rewrite E0, EYrg; lia).
  assert (EXgp : X (RotGrid pc pr ⊕ (py, px)) = px)
    by (assert (E0 : X (RotGrid pc pr ⊕ (py, px)) = X (RotGrid pc pr) + px) by reflexivity;
        rewrite E0, EXrg; lia).
  assert (EHgp : H (RotGrid pc pr ⊕ (py, px)) = PW)
    by (assert (E0 : H (RotGrid pc pr ⊕ (py, px)) = H (RotGrid pc pr)) by reflexivity;
        rewrite E0, EHrg; reflexivity).
  assert (EWgp : W (RotGrid pc pr ⊕ (py, px)) = PW)
    by (assert (E0 : W (RotGrid pc pr ⊕ (py, px)) = W (RotGrid pc pr)) by reflexivity;
        rewrite E0, EWrg; reflexivity).
  assert (Hgp : L (RotGrid pc pr ⊕ (py, px)) (py + ry) (px + rx) = true). {
    unfold GridTranslate; simpl.
    replace (py + ry - py) with ry by lia.
    replace (px + rx - px) with rx by lia.
    exact HL.
  }
  assert (Hbox : InBox (RotGrid pc pr ⊕ (py, px)) (py + ry) (px + rx) = true). {
    apply InBoxTrue.
    rewrite EYgp, EXgp, EHgp, EWgp; keep_only Hry Hrx; lia.
  }
  destruct (GridIncludeElim _ _ E1 (py + ry) (px + rx) Hbox Hgp) as [HboxFull _].
  apply InBoxTrue in HboxFull as [[Hy1 _] _].
  assert (EYFull : Y (Full g) = Y g) by reflexivity.
  rewrite EYFull, HY in Hy1.
  keep_only Hy1 Hry HP; lia.
Qed.

(* A successful FixPiece proves its own guard held. *)
Lemma FixPieceGameoverFalse : ∀ (p_new : Piece) (s s' : State)
  (Hn : FixPiece p_new s = Some s'),
  gameover s = false.
Proof.
  intros p_new s s' Hn.
  cbv beta iota zeta delta [FixPiece] in Hn.
  destruct (! gameover s && ! CanMovePiece (-1, 0) s) eqn: E; [ | discriminate Hn ].
  apply andb_true_iff in E as [E1 _]; apply negb_true_iff in E1; exact E1.
Qed.

(* A successful MovePiece proves its own guard held. *)
Lemma MovePieceNotGameover : ∀ [s s' dyx]
  (H1 : MovePiece dyx s = Some s'),
  gameover s = false.
Proof.
  intros; unfold MovePiece in H1.
  destruct (! gameover s && CanMovePiece dyx s) eqn: E; [ | destruct dyx; discriminate H1].
  apply andb_true_iff in E as [E1 _]; apply negb_true_iff in E1; exact E1.
Qed.

(* A successful RotatePiece proves its own guard held. *)
Lemma RotatePieceNotGameover : ∀ [s s' cw]
  (H1 : RotatePiece cw s = Some s'),
  gameover s = false.
Proof.
  intros; unfold RotatePiece in H1.
  destruct (! gameover s && Valid (mg s) (p s) (pyx s) ((pr s + (if cw then -1 else 1)) mod 4)) eqn: E;
    [ | discriminate H1].
  apply andb_true_iff in E as [E1 _]; apply negb_true_iff in E1; exact E1.
Qed.

(* Rotating after an arbitrary relocation preserves Correct, needing only the
 * three "shape" conjuncts of Correct at the pre-relocation state (TypeOK,
 * Gameover, NoFullLine), not PieceOccupiedInsideBounds/PieceOnFreeBlocks.
 * This matters for wall kicks (T6): NewPieceYXState may relocate the piece to
 * a position that is not itself Valid at the current pr (that is the whole
 * point of a kick: the relocation is a mere candidate, validated only by
 * whether the subsequent rotation succeeds), so Correct of the relocated,
 * unrotated state cannot in general be assumed. But RotatePieceValid and
 * ValidPieceInvariants never use it either: whatever position rotation
 * succeeds from, its own success re-establishes the two piece invariants from
 * scratch, via Valid at the new pr. Only TypeOK/Gameover/NoFullLine are
 * literally copied through from mg/gameover, which NewPieceYXState leaves
 * untouched; hence the weaker hypothesis suffices.
 * The extra `gameover s' = gameover s` conclusion is exposed because it is
 * needed again, unchanged, by callers threading this fact up through further
 * layers (T6Proofs.v, for a GameoverImplyNotSwapped-style invariant). *)
Lemma RotateAfterRelocateCorrect : ∀ (pyxNew : ℤ × ℤ) (cw : bool) (s s' : State)
  (H1 : TypeOK s)
  (H2 : Gameover s)
  (H3 : NoFullLine s)
  (Hn : RotatePiece cw (NewPieceYXState pyxNew s) = Some s'),
  Correct s' ∧ gameover s' = gameover s.
Proof.
  intros pyxNew cw s s' H1 H2 H3 Hn.
  assert (Emg : mg (NewPieceYXState pyxNew s) = mg s) by reflexivity.
  assert (Ego : gameover (NewPieceYXState pyxNew s) = gameover s) by reflexivity.
  assert (Epr : pr (NewPieceYXState pyxNew s) = pr s) by reflexivity.
  set (R := RotatePieceOK cw (NewPieceYXState pyxNew s) s' Hn).
  assert(Emg' : mg s' = mg (NewPieceYXState pyxNew s)) by now keep_only R; tauto.
  assert(Ep' : p s' = p (NewPieceYXState pyxNew s)) by now keep_only R; tauto.
  assert(Epyx' : pyx s' = pyx (NewPieceYXState pyxNew s)) by now keep_only R; tauto.
  assert(Ego' : gameover s' = gameover (NewPieceYXState pyxNew s)) by now keep_only R; tauto.
  assert(Epr' : pr s' = (pr (NewPieceYXState pyxNew s) + (if cw then -1
      else 1)) mod 4) by now keep_only R; tauto.
  assert (HV : Valid (mg s') (p s') (pyx s') (pr s') = true)
    by (eapply RotatePieceValid; eassumption).
  assert (HgoFinal : gameover s' = gameover s) by (rewrite Ego', Ego; reflexivity).
  split; [ | exact HgoFinal ].
  assert (Hb : 0 ≤ (pr s + (if cw then -1 else 1)) mod 4 < 4)
        by (apply Z.mod_pos_bound; lia).
  assert (L1 : TypeOK s'). {
    apply TypeOKSpec; split_top;
      (rewrite Emg', Emg; keep_only H1; destruct (TypeOKSpec s); tauto) ||
      (rewrite Epr', Epr; lia).
  }
  assert (L2 : PieceOccupiedInsideBounds s')
    by now destruct (ValidPieceInvariants s' HV); tauto.
  assert (L3 : PieceOnFreeBlocks s')
    by now destruct (ValidPieceInvariants s' HV); tauto.
  assert (L4 : NoFullLine s')
    by now unfold NoFullLine in *; rewrite Emg', Emg; exact H3.
  assert (L5 : Gameover s')
    by now unfold Gameover in *; rewrite HgoFinal, Emg', Emg; exact H2.
  apply CorrectSpec; split_top; auto using L1, L2, L3, L4, L5.
Qed.

(* Same as RotateAfterRelocateCorrect, but from CorrectWithoutGameover instead
of full Correct. As noted above, RotatePieceValid/ValidPieceInvariants never
use Gameover at all; the only place Gameover appeared was L5 (needed to
conclude the full Correct s'), which this version simply drops in favor of
concluding CorrectWithoutGameover s' directly. *)
Lemma RotateAfterRelocateCorrectWithoutGameover : ∀ (pyxNew : ℤ × ℤ) (cw : bool) (s s' : State)
  (H1 : CorrectWithoutGameover s)
  (Hn : RotatePiece cw (NewPieceYXState pyxNew s) = Some s'),
  CorrectWithoutGameover s' ∧ gameover s' = gameover s ∧ mg s' = mg s.
Proof.
  intros pyxNew cw s s' H1 Hn.
  destruct H1 as (HT & _ & _ & HN).
  assert (Emg : mg (NewPieceYXState pyxNew s) = mg s) by reflexivity.
  assert (Ego : gameover (NewPieceYXState pyxNew s) = gameover s) by reflexivity.
  assert (Epr : pr (NewPieceYXState pyxNew s) = pr s) by reflexivity.
  set (R := RotatePieceOK cw (NewPieceYXState pyxNew s) s' Hn).
  assert(Emg' : mg s' = mg (NewPieceYXState pyxNew s)) by now keep_only R; tauto.
  assert(Ep' : p s' = p (NewPieceYXState pyxNew s)) by now keep_only R; tauto.
  assert(Epyx' : pyx s' = pyx (NewPieceYXState pyxNew s)) by now keep_only R; tauto.
  assert(Ego' : gameover s' = gameover (NewPieceYXState pyxNew s)) by now keep_only R; tauto.
  assert(Epr' : pr s' = (pr (NewPieceYXState pyxNew s) + (if cw then -1
      else 1)) mod 4) by now keep_only R; tauto.
  assert (HV : Valid (mg s') (p s') (pyx s') (pr s') = true)
    by (eapply RotatePieceValid; eassumption).
  assert (HgoFinal : gameover s' = gameover s) by (rewrite Ego', Ego; reflexivity).
  assert (HmgFinal : mg s' = mg s) by (rewrite Emg', Emg; reflexivity).
  split; [ | split; [exact HgoFinal | exact HmgFinal]].
  assert (Hb : 0 ≤ (pr s + (if cw then -1 else 1)) mod 4 < 4)
        by (apply Z.mod_pos_bound; lia).
  assert (L1 : TypeOK s'). {
    apply TypeOKSpec; split_top;
      (rewrite Emg', Emg; keep_only HT; destruct (TypeOKSpec s); tauto) ||
      (rewrite Epr', Epr; lia).
  }
  assert (L2 : PieceOccupiedInsideBounds s')
    by now destruct (ValidPieceInvariants s' HV); tauto.
  assert (L3 : PieceOnFreeBlocks s')
    by now destruct (ValidPieceInvariants s' HV); tauto.
  assert (L4 : NoFullLine s')
    by now unfold NoFullLine in *; rewrite Emg', Emg; exact HN.
  unfold CorrectWithoutGameover; split; [ | split; [ | split]]; assumption.
Qed.
