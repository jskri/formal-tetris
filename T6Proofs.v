From Tetris Require Import T6 Notations.
From Tetris Require T1 T2 T3 T4 T5 T1Proofs T2Proofs T3Proofs T4Proofs T5Proofs.
From Stdlib Require Import Lia PeanoNat ZArith.

Module T1P := T1Proofs.
Module T2P := T2Proofs.
Module T3P := T3Proofs.
Module T4P := T4Proofs.
Module T5P := T5Proofs.

(* The T1, T2 and T3 parts of a T6 state. *)
Local Notation s3 s := (T4.s3 (T5.s4 s)).
Local Notation s2 s := (T3.s2 (s3 s)).
Local Notation s1 s := (T2.s1 (s2 s)).


(* ========================================================================= *)
(* The kick candidate                                                        *)
(*                                                                           *)
(* A wall kick rotates the piece after relocating it to a position that need *)
(* not be Valid: the relocation is a mere candidate, validated only by       *)
(* whether the rotation succeeds. The relocated state is therefore not       *)
(* Correct in general, and the T5 lemmas on RotatePiece do not apply.        *)
(* Instead, the T1 part is covered by T1Proofs' RotateAfterRelocate lemmas,  *)
(* the T2-T4 invariants read only fields that neither the relocation nor the *)
(* rotation touch, and the T5 ones follow from the recomputed shadow.        *)
(* ========================================================================= *)

(* The T1 part of a kick is a T1 rotation after a T1 relocation. All other
 * fields are those of the starting state, and the shadow is recomputed. *)
Lemma KickStep : ∀ [pyxNew cw] [s s' : State]
  (Hn : T5.RotatePiece cw (T5.NewPieceYXState pyxNew s) = Some s'),
    T1.RotatePiece cw (T1.NewPieceYXState pyxNew (s1 s)) = Some (s1 s')
  ∧ T2.level (s2 s') = T2.level (s2 s)
  ∧ T2.totalClearedLines (s2 s') = T2.totalClearedLines (s2 s)
  ∧ T3.hold (s3 s') = T3.hold (s3 s)
  ∧ T3.swapped (s3 s') = T3.swapped (s3 s)
  ∧ T4.d (T5.s4 s') = T4.d (T5.s4 s)
  ∧ T5.GyEqShadowY s'.
Proof.
  intros.
  assert (HG : T5.GyEqShadowY s') by eapp T5P.UpdateShadowYGuardGyEqShadowY.
  apply T5P.RotatePieceStep in Hn; decompose [ex and] Hn; subst.
  repeat match goal with
  | E : T4.RotatePiece _ _ = Some _ |- _ => apply T4P.RotatePieceStep in E
  | E : T3.RotatePiece _ _ = Some _ |- _ => apply T3P.RotatePieceStep in E
  | E : T2.RotatePiece _ _ = Some _ |- _ => apply T2P.RotatePieceStep in E
  | H : _ ∧ _ |- _ => destruct H
  end.
  split_top; first [ assumption | symmetry; assumption ].
Qed.

(* The T2-T4 invariants hold after a kick, given the T1 ones: the fields they
 * read beyond T1 are unchanged, and so is gameover. *)
#[local] Ltac lift_kick_T4 :=
  match goal with
  | Hn : T5.RotatePiece _ _ = Some _ |- _ => apply KickStep in Hn; decompose [and] Hn
  end;
  unfold T4.Correct, T3.Correct, T2.Correct,
    T4.CorrectWithoutGameover, T3.CorrectWithoutGameover, T2.CorrectWithoutGameover,
    T2.LevelCorrect, T3.SwappedImplyHoldSome, T3.GameoverImplyNotSwapped,
    T3.gameover in *;
  repeat match goal with E : _ = _ |- _ => rewrite E end;
  tauto.

Lemma KickCorrectWithoutGameover : ∀ [pyxNew cw] [s s' : State]
  (Hc : T5.CorrectWithoutGameover s)
  (Hn : T5.RotatePiece cw (T5.NewPieceYXState pyxNew s) = Some s'),
  T5.CorrectWithoutGameover s' ∧ T5.mg s' = T5.mg s ∧ T5.gameover s' = T5.gameover s.
Proof.
  intros.
  assert (HG : T5.GyEqShadowY s') by (apply KickStep in Hn; tauto).
  assert (E1 : T1.RotatePiece cw (T1.NewPieceYXState pyxNew (s1 s)) = Some (s1 s'))
    by (apply KickStep in Hn; tauto).
  assert (HC1 : T1.CorrectWithoutGameover (s1 s)) by (
    unfold T5.CorrectWithoutGameover, T4.CorrectWithoutGameover,
      T3.CorrectWithoutGameover, T2.CorrectWithoutGameover in Hc; tauto).
  assert (HC1' : T1.CorrectWithoutGameover (s1 s'))
    by (apply T1P.RotateAfterRelocateCorrectWithoutGameover in E1; tauto).
  assert (Ego1 : T1.gameover (s1 s') = T1.gameover (s1 s))
    by (apply T1P.RotateAfterRelocateCorrectWithoutGameover in E1; tauto).
  assert (Emg1 : T1.mg (s1 s') = T1.mg (s1 s))
    by (apply T1P.RotateAfterRelocateCorrectWithoutGameover in E1; tauto).
  assert (HC4 : T4.CorrectWithoutGameover (T5.s4 s))
    by (unfold T5.CorrectWithoutGameover in Hc; tauto).
  assert (HC4' : T4.CorrectWithoutGameover (T5.s4 s')) by lift_kick_T4.
  assert (HC' : T5.CorrectWithoutGameover s') by eapp T5P.LiftCorrectWithoutGameover.
  split_top; assumption.
Qed.

Lemma KickCorrect : ∀ [pyxNew cw] [s s' : State]
  (Hc : T5.Correct s)
  (Hn : T5.RotatePiece cw (T5.NewPieceYXState pyxNew s) = Some s'),
  T5.Correct s'.
Proof.
  intros.
  assert (HG : T5.GyEqShadowY s') by (apply KickStep in Hn; tauto).
  assert (E1 : T1.RotatePiece cw (T1.NewPieceYXState pyxNew (s1 s)) = Some (s1 s'))
    by (apply KickStep in Hn; tauto).
  assert (HC1 : T1.Correct (s1 s)) by (
    unfold T5.Correct, T4.Correct, T3.Correct, T2.Correct in Hc; tauto).
  unfold T1.Correct, T1.CorrectWithoutGameover in HC1.
  assert (HC1' : T1.Correct (s1 s'))
    by (apply T1P.RotateAfterRelocateCorrect in E1; tauto).
  assert (Ego1 : T1.gameover (s1 s') = T1.gameover (s1 s))
    by (apply T1P.RotateAfterRelocateCorrect in E1; tauto).
  assert (HC4 : T4.Correct (T5.s4 s)) by (unfold T5.Correct in Hc; tauto).
  assert (HC4' : T4.Correct (T5.s4 s')) by lift_kick_T4.
  eapp T5P.LiftCorrect.
Qed.


(* ========================================================================= *)
(* RotateKickPiece                                                           *)
(* ========================================================================= *)

(* A successful wall kick is a kick candidate (one block left or right) whose
 * rotation succeeded, and its guard proves the game is not over. *)
Lemma RotateKickPieceCases : ∀ [s s' cw]
  (Hn : RotateKickPiece cw s = Some s'),
    gameover s = false
  ∧ ∃ pyxNew, T5.RotatePiece cw (T5.NewPieceYXState pyxNew s) = Some s'.
Proof.
  intros; unfold RotateKickPiece in Hn; cbv zeta in Hn.
  destruct (T5.gameover s) eqn: Ego, (T5.RotatePiece cw s);
    cbn [negb andb] in Hn; try discriminate Hn.
  (* left candidate, else right candidate *)
  destruct T5.RotatePiece eqn: El; [ inject Hn; subst | ];
    split_top; first [ assumption | eexists; eassumption ].
Qed.

Lemma RotateKickPieceCorrect : ∀ [s s' cw]
  (Hc : Correct s)
  (Hn : RotateKickPiece cw s = Some s'),
  Correct s'.
Proof. intros; apply RotateKickPieceCases in Hn; decompose [ex and] Hn; eapp KickCorrect. Qed.

Lemma RotateKickPieceCorrectWithoutGameover : ∀ [s s' cw]
  (Hc : CorrectWithoutGameover s)
  (Hn : RotateKickPiece cw s = Some s'),
  CorrectWithoutGameover s'.
Proof.
  intros; apply RotateKickPieceCases in Hn; decompose [ex and] Hn.
  match goal with E : T5.RotatePiece _ _ = Some _ |- _ =>
    apply KickCorrectWithoutGameover in E end; first [ assumption | tauto ].
Qed.

Lemma RotateKickPieceMgGameoverUnchanged : ∀ [s s' cw]
  (Hc : CorrectWithoutGameover s)
  (Hn : RotateKickPiece cw s = Some s'),
  mg s' = mg s ∧ gameover s' = gameover s.
Proof.
  intros; apply RotateKickPieceCases in Hn; decompose [ex and] Hn.
  match goal with E : T5.RotatePiece _ _ = Some _ |- _ =>
    apply KickCorrectWithoutGameover in E end; first [ assumption | tauto ].
Qed.


(* ========================================================================= *)
(* State invariants                                                          *)
(* ========================================================================= *)

Lemma InitCorrect : ∀ (bags : ℕ → ℕ → T1.Piece) (H : ∀ i, T4.PieceSet (bags i)),
  Correct (Init bags H).
Proof. intros; apply T5P.InitCorrect. Qed.

Lemma NextCorrect : ∀ [e : Event] [s s' : State]
  (Hc : Correct s)
  (Hn : Next e s = Some s'),
  Correct s'.
Proof.
  intros; destruct e; cbn [Next NextT5Event] in Hn;
    first [ eapp T5P.NextCorrect | eapp RotateKickPieceCorrect ].
Qed.

Theorem SpecCorrect : ∀ e s s',
    (∀ bags H, Correct (Init bags H))
  ∧ (Correct s → Next e s = Some s' → Correct s').
Proof. split_top; eauto using InitCorrect, NextCorrect. Qed.


(* ========================================================================= *)
(* Step invariants                                                           *)
(* ========================================================================= *)

Theorem CorrectStepHolds : ∀ s s'
  (Hc : Correct s),
  CorrectStep s s'.
Proof. intros; apply T5P.StepCorrect; exact Hc. Qed.


(* ========================================================================= *)
(* Refinement                                                                *)
(* ========================================================================= *)

Lemma InitRefine : ∀ bags HSet, fₛ (T6.Init bags HSet) = T5.Init bags HSet.
Proof. reflexivity. Qed.

(*
         e5
   s5    →    s5'
fₛ ↑     ⇑fₑ  ↑ fₛ
   s6    →    s6'
         e5
*)

Lemma NextRefine : ∀ e5 s6 s6'
  (H1 : NextT5Event e5 s6 = Some s6'),
  T6.NextT5Event (fₑ e5) (fₛ s6) = Some (fₛ s6').
Proof. intros; exact H1. Qed.

Theorem T6RefinesT5Holds : T6RefinesT5.
Proof. unfold T6RefinesT5; split_top; auto using InitRefine, NextRefine. Qed.


(* ========================================================================= *)
(* Helpers for refining models                                               *)
(* ========================================================================= *)

Lemma RotateKickNotGameover : ∀ [s s' cw]
  (H1 : RotateKickPiece cw s = Some s'),
  gameover s = false.
Proof. intros; apply RotateKickPieceCases in H1; tauto. Qed.
