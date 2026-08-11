From Stdlib Require Import
  Unicode.Utf8
  ZArith
  Lia
  List.
From Tetris Require Import Notations Quantifiers.

(* [Z.of_nat (Z.to_nat z)] is [z] clipped to the non-negative integers.
 * (Stdlib may already provide this as [Z2Nat.id_max].) *)
Lemma ZOfNatToNat : ∀ z : ℤ, Z.of_nat (Z.to_nat z) = Z.max 0 z.
Proof.
  intro z; destruct z as [| q | q]; simpl; try rewrite positive_nat_Z; lia.
Qed.

(* The membership characterisation of [seqz]. Everything else is a corollary. *)
Lemma InSeqz : ∀ start len y : ℤ,
  In y (seqz start len) ↔ start ≤ y < start + len.
Proof.
  intros start len y; unfold seqz; rewrite in_map_iff; split.
  - intros [n [Hn Hin]].
    apply in_seq in Hin.
    (* [Hin] lives in ℕ; move it to ℤ, then clip [Z.to_nat len]. *)
    assert (L1 : Z.of_nat n < Z.of_nat (Z.to_nat len)) by lia.
    rewrite ZOfNatToNat in L1.
    assert (L2 : 0 ≤ Z.of_nat n) by lia.
    lia.
  - intros Hy.
    exists (Z.to_nat (y - start)).
    assert (L1 : Z.of_nat (Z.to_nat (y - start)) = y - start)
      by (rewrite ZOfNatToNat; lia).
    split; [ lia | ].
    apply in_seq.
    assert (L2 : Z.of_nat (Z.to_nat (y - start)) < Z.of_nat (Z.to_nat len))
      by (rewrite L1, ZOfNatToNat; lia).
    lia.
Qed.

Lemma forallbzForall : ∀ (f : ℤ → bool) (start len : ℤ),
  forallbz f (seqz start len) = true ↔ (∀ y, start ≤ y < start + len → f y = true).
Proof.
  intros f start len; unfold forallbz; rewrite forallb_forall; split.
  - intros Hall y Hy; apply Hall; apply InSeqz; exact Hy.
  - intros Hall y Hy; apply Hall; apply InSeqz; exact Hy.
Qed.

Lemma forallbzIntro : ∀ (f : ℤ → bool) (start len : ℤ),
  (∀ y, start ≤ y < start + len → f y = true) → forallbz f (seqz start len) = true.
Proof.
  intros f start len Hall; apply forallbzForall; exact Hall.
Qed.

Lemma forallbzElim : ∀ (f : ℤ → bool) (start len : ℤ),
  forallbz f (seqz start len) = true → ∀ y, start ≤ y < start + len → f y = true.
Proof.
  intros f start len Hall; apply forallbzForall; exact Hall.
Qed.

Lemma forallbz2Forall : ∀ (f : ℤ → ℤ → bool) (sy ly sx lx : ℤ),
  forallbz2 f (seqz sy ly) (seqz sx lx) = true
  ↔ (∀ y x, sy ≤ y < sy + ly → sx ≤ x < sx + lx → f y x = true).
Proof.
  intros f sy ly sx lx; unfold forallbz2; rewrite forallbzForall; split.
  - intros Hall y x Hy Hx.
    assert (L1 : forallbz (f y) (seqz sx lx) = true) by (apply Hall; exact Hy).
    apply (forallbzElim _ _ _ L1); exact Hx.
  - intros Hall y Hy; apply forallbzIntro; intros x Hx; apply Hall; assumption.
Qed.


Lemma forallbnForall : ∀ (f : ℤ → bool) (l1 : ℤ),
  forallbn f (seqn 0 l1) = true
  ↔ ∀ x : ℕ, Z.of_nat x < l1 → f (Z.of_nat x) = true.
Proof.
  intros f l1.
  unfold forallbn.
  rewrite forallb_forall.
  split. intros H x Hx.
  - apply H.
    unfold seqn.
    rewrite in_seq. lia.
  - intros H x Hx.
    unfold seqn in Hx. rewrite in_seq in Hx. apply H. lia.
Qed.

Lemma forallbn2Forall : ∀ f (l1 l2 : ℤ),
  forallbn2 f (seqn 0 l1) (seqn 0 l2) = true
  ↔ ∀ y x : ℤ, (0 ≤ y ∧ y < l1) ∧ (0 ≤ x ∧ x < l2) → f y x = true.
Proof.
 intros f l1 l2.
  unfold forallbn2.
  rewrite forallbnForall.
  split.
  - intros H y x [[Hy0 Hyl] [Hx0 Hxl]].
    assert (Heqy : Z.of_nat (Z.to_nat y) = y) by (apply Z2Nat.id; lia).
    assert (Heqx : Z.of_nat (Z.to_nat x) = x) by (apply Z2Nat.id; lia).
    assert (Hyn : Z.of_nat (Z.to_nat y) < l1) by (rewrite Heqy; exact Hyl).
    specialize (H _ Hyn).
    rewrite forallbnForall in H.
    assert (Hxn : Z.of_nat (Z.to_nat x) < l2) by (rewrite Heqx; exact Hxl).
    specialize (H _ Hxn).
    rewrite Heqy, Heqx in H. exact H.
  - intros H ? ?.
    rewrite forallbnForall.
    intros; apply H; lia || assumption.
Qed.

#[local] Lemma existsbnExistsTrue : ∀ (f : ℤ → bool) (l1 : ℤ),
  existsbn f (seqn 0 l1) = true
  ↔ ∃ n : ℕ, Z.of_nat n < l1 ∧ f (Z.of_nat n) = true.
Proof.
  intros f l1. unfold existsbn.
  rewrite existsb_exists.
  split.
  - intros [n [Hin Hf]].
    exists n. split.
    + unfold seqn in Hin. rewrite in_seq in Hin. lia.
    + exact Hf.
  - intros [n [Hlt Hf]].
    exists n. split.
    + unfold seqn. rewrite in_seq. lia.
    + exact Hf.
Qed.

(* simplify *)
(* 2D version: existsbn2 = true ↔ ∃ y x in bounds, f y x = true. *)
#[local] Lemma existsbn2ExistsTrue : ∀ f (l1 l2 : ℤ),
  existsbn2 f (seqn 0 l1) (seqn 0 l2) = true
  ↔ ∃ y x : ℤ, (0 ≤ y ∧ y < l1) ∧ (0 ≤ x ∧ x < l2) ∧ f y x = true.
Proof.
  intros f l1 l2.
  unfold existsbn2.
  rewrite existsbnExistsTrue.
  split.
  - intros [yn [Hyn Hinner]].
    rewrite existsbnExistsTrue in Hinner.
    destruct Hinner as [xn [Hxn Hf]].
    exists (Z.of_nat yn), (Z.of_nat xn).
    repeat split; lia || assumption.
  - intros [y [x [[Hy0 Hyl] [[Hx0 Hxl] Hf]]]].
    assert (Heqy : Z.of_nat (Z.to_nat y) = y) by (apply Z2Nat.id; lia).
    assert (Heqx : Z.of_nat (Z.to_nat x) = x) by (apply Z2Nat.id; lia).
    exists (Z.to_nat y). split.
    + rewrite Heqy. exact Hyl.
    + rewrite existsbnExistsTrue.
      exists (Z.to_nat x). split.
      * rewrite Heqx. exact Hxl.
      * rewrite Heqy, Heqx. exact Hf.
Qed.

Lemma existsbn2FalseNotExists : ∀ f (l1 l2 : ℤ),
  existsbn2 f (seqn 0 l1) (seqn 0 l2) = false
  ↔ ¬ (∃ y x : ℤ, (0 ≤ y ∧ y < l1) ∧ (0 ≤ x ∧ x < l2) ∧ f y x = true).
Proof.
  intros f l1 l2.
  pose proof (existsbn2ExistsTrue f l1 l2) as [Hfwd Hbwd].
  split.
  - intros Hfalse Hexists.
    rewrite (Hbwd Hexists) in Hfalse. discriminate.
  - intros Hnot.
    destruct (existsbn2 f (seqn 0 l1) (seqn 0 l2)) eqn:E.
    + exfalso. apply Hnot. apply Hfwd. auto.
    + reflexivity.
Qed.
