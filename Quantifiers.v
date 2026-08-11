(* Boolean versions of the universal quantifier over integer ranges. *)

From Stdlib Require Import
  Unicode.Utf8
  ZArith (* Z.of_nat, Z.to_nat *)
  List (* for forallb, existsb *)
  Program.Basics. (* for ∘ *)
From Tetris Require Import Notations.

Open Scope program_scope.

(* [seqz start len] is the list [start; start+1; ...; start+len-1].
 * [start] may be negative. A non-positive [len] yields the empty list.
 *
 * Note: the previous definition returned a [list ℕ] and truncated a negative
 * [start] to 0, which silently dropped the negative part of a grid box (and
 * overshot its top). Grid boxes have negative origins as soon as a piece is
 * translated below or to the left of the main grid, hence the change. *)
Definition seqz (start len : ℤ) : list ℤ :=
  map (λ n : ℕ, start + Z.of_nat n) (seq 0 (Z.to_nat len)).

Definition forallbz (f : ℤ → bool) (xs : list ℤ) : bool :=
  forallb f xs.

(* 2D forallb over two ranges *)
Definition forallbz2 (f : ℤ → ℤ → bool) (ys xs : list ℤ) : bool :=
  forallbz (λ y, forallbz (f y) xs) ys.

(* start and len are expected to be non-negative.
   Negative values are truncated to 0. *)
Definition seqn (start len : ℤ) : list ℕ :=
  seq (Z.to_nat start) (Z.to_nat len).

Definition forallbn (f : ℤ → bool) (xs : list ℕ) : bool :=
  forallb (f ∘ Z.of_nat) xs.

Definition forallbn2 (f : ℤ → ℤ → bool) (ys xs : list ℕ) : bool :=
  forallbn (λ y, forallbn (f y) xs) ys.

Definition existsbn (f : ℤ → bool) (xs : list ℕ) : bool :=
  existsb (f ∘ Z.of_nat) xs.

(* Helper: 2D existsb over two ranges *)
Definition existsbn2 (f : ℤ → ℤ → bool) (ys xs : list ℕ) : bool :=
  existsbn (λ y, existsbn (f y) xs) ys.