From Stdlib Require Import Unicode.Utf8 ZArith Bool Arith.
Export Unicode.Utf8 ZArith Bool Arith.

Notation ℤ := Z.
Notation ℕ := nat.

Open Scope Z.
Infix "≤" := Z.le : Z_scope.
Infix "≥" := Z.ge : Z_scope.
Notation "a ≤? b" := (a <=? b) (at level 70, no associativity).
Notation "a ≤ b < c" := (a <= b < c) (at level 70, no associativity).
Notation "a ≤ b ≤ c" := (a <= b <= c) (at level 70, no associativity).
Notation "a < b ≤ c" := (a < b <= c) (at level 70, no associativity).
Notation "a ≤? b <? c" := ((a ≤? b) && (b <? c)) (at level 70, no associativity).
Notation "! a" := (negb a) (at level 39, no associativity). (* && has level 40 *)
Notation "a ≠? b" := (! (a =? b)) (at level 70, no associativity). (* =? has level 70 *)
Notation "A × B" := (prod A B) (at level 50, left associativity) : type_scope.
Notation "f ** n" := (Nat.iter n f) (at level 31, left associativity).

Tactic Notation "keep_only" ne_hyp_list(hs) := clear - hs.

Ltac split_top :=
  match goal with
  | |- _ ∧ _ => split; [ |split_top]
  | |- _ => idtac
  end.

Ltac eapp L :=
  eapply L; eassumption.

Ltac inject H :=
  injection H; clear H; intro H.