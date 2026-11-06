From Tetris Require Import T5 Notations.
From Tetris Require T1 T2 T3 T4 T1Proofs T2Proofs T3Proofs T4Proofs.
From Stdlib Require Import Lia PeanoNat ZArith.
Import T1(Piece, PW, Grid, Valid, ForbiddenGrid).
Import (notations) T1.

Module T1P := T1Proofs.
Module T2P := T2Proofs.
Module T3P := T3Proofs.
Module T4P := T4Proofs.

(* ========================================================================= *)
(* The shadow search                                                         *)
(* ========================================================================= *)

(* ShadowYImpl descends while Valid holds one row lower, and stops as soon as
 * it does not. As long as the fuel is large enough to reach the floor 1-PW
 * (below which nothing is Valid, see T1Proofs' ValidBelowFloor), the search
 * stops at the highest row from which the piece cannot go down. *)
Lemma ShadowYImplSpec : ∀ (fuel : ℕ) (g : Grid) (pc : Piece) (y0 x0 pr0 : ℤ)
  (HTY : T1.Y g = 0)
  (HR : 0 ≤ pr0 < 4)
  (HV0 : Valid g pc (y0, x0) pr0 = true)
  (HF : y0 - Z.of_nat fuel ≤ 1 - PW),
  let y' := ShadowYImpl fuel g pc y0 x0 pr0 in
    y' ≤ y0
  ∧ Valid g pc (y', x0) pr0 = true
  ∧ Valid g pc (y' - 1, x0) pr0 = false
  ∧ (∀ y, y ≤ y0 →
      Valid g pc (y, x0) pr0 = true →
      Valid g pc (y - 1, x0) pr0 = false →
      y ≤ y').
Proof.
  induction fuel as [| fuel IH]; intros g pc y0 x0 pr0 HTY HR HV0 HF; cbv zeta;
    cbn [ShadowYImpl].
  - (* no fuel left: y0 is on the floor, one row lower is out of the grid *)
    assert (HV1 : Valid g pc (y0 - 1, x0) pr0 = false)
      by (apply T1P.ValidBelowFloor; (assumption || lia)).
    split_top; first [ assumption | intros; lia ].
  - destruct (Valid g pc (y0 - 1, x0) pr0) eqn: Hstep; cbn [negb].
    + (* Valid one row lower: the search goes on from there *)
      assert (HF' : y0 - 1 - Z.of_nat fuel ≤ 1 - PW) by lia.
      assert (IH' := IH g pc (y0 - 1) x0 pr0); cbv zeta in IH'.
      apply IH' in HF'; try assumption; decompose [and] HF'.
      split_top; first [ assumption | lia | intros y Hy HVy HVy1 ].
      (* y0 itself cannot go down, so any such row is at most y0 - 1 *)
      destruct (Z.eq_dec y y0); [ congruence | ].
      match goal with Hm : ∀ y, y ≤ y0 - 1 → _ |- _ => apply Hm end;
        (assumption || lia).
    + (* not Valid one row lower: the search stops at y0 *)
      split_top; first [ assumption | intros; lia ].
Qed.

(* Either the search stops (Valid fails one row lower), or it uses up all its
 * fuel. No hypothesis on the starting position is needed. *)
Lemma ShadowYImplStopsOrExhausts : ∀ (fuel : ℕ) (g : Grid) (pc : Piece) (y0 x0 pr0 : ℤ),
    Valid g pc (ShadowYImpl fuel g pc y0 x0 pr0 - 1, x0) pr0 = false
  ∨ ShadowYImpl fuel g pc y0 x0 pr0 = y0 - Z.of_nat fuel.
Proof.
  induction fuel as [| fuel IH]; intros; cbn [ShadowYImpl].
  - right; lia.
  - destruct (Valid g pc (y0 - 1, x0) pr0) eqn: Hstep; cbn [negb];
      decompose [or] (IH g pc (y0 - 1) x0 pr0);
      first [ left; assumption | right; lia ].
Qed.

(* Either the search does not move, or it ends on a Valid position. *)
Lemma ShadowYImplValidOrNoMove : ∀ (fuel : ℕ) (g : Grid) (pc : Piece) (y0 x0 pr0 : ℤ),
    ShadowYImpl fuel g pc y0 x0 pr0 = y0
  ∨ Valid g pc (ShadowYImpl fuel g pc y0 x0 pr0, x0) pr0 = true.
Proof.
  induction fuel as [| fuel IH]; intros; cbn [ShadowYImpl].
  - left; reflexivity.
  - destruct (Valid g pc (y0 - 1, x0) pr0) eqn: Hstep; cbn [negb];
      decompose [or] (IH g pc (y0 - 1) x0 pr0);
      first [ left; reflexivity | right; congruence ].
Qed.

(* A stopped search is a no-op when restarted from its own result. *)
Lemma ShadowYImplNoOpWhenStopped : ∀ (fuel : ℕ) (g : Grid) (pc : Piece) (y x pr : ℤ)
  (HS : Valid g pc (y - 1, x) pr = false),
  ShadowYImpl fuel g pc y x pr = y.
Proof. intros; destruct fuel; cbn [ShadowYImpl]; try rewrite HS; reflexivity. Qed.

(* The fuel of ShadowY always reaches the floor 1-PW: exactly when py ≥ 0,
 * with room to spare when py < 0 (Z.to_nat clamps py to 0). *)
Lemma ShadowYFuelSufficient : ∀ (py0 : ℤ),
  py0 - Z.of_nat (Z.to_nat py0 + Z.to_nat PW - 1) ≤ 1 - PW.
Proof. intros; pose proof T1.AxiomsPW; lia. Qed.


(* ========================================================================= *)
(* The shadow of a T4 state                                                  *)
(* ========================================================================= *)

Lemma T4CorrectWithoutGameover : ∀ [s4 : T4.State]
  (Hc4 : T4.Correct s4),
  T4.CorrectWithoutGameover s4.
Proof.
  intros; unfold T4.Correct, T3.Correct, T2.Correct, T1.Correct in Hc4.
  unfold T4.CorrectWithoutGameover, T3.CorrectWithoutGameover,
    T2.CorrectWithoutGameover; tauto.
Qed.

(* The facts on the main grid and the rotation that the search needs. *)
Lemma T4TypeFacts : ∀ [s4 : T4.State]
  (Hc4 : T4.CorrectWithoutGameover s4),
  T1.Y (T4.mg s4) = 0 ∧ 0 ≤ T4.pr s4 < 4.
Proof.
  intros.
  assert (HT : T1.TypeOK (T2.s1 (T3.s2 (T4.s3 s4)))) by (
    unfold T4.CorrectWithoutGameover, T3.CorrectWithoutGameover,
      T2.CorrectWithoutGameover, T1.CorrectWithoutGameover in Hc4; tauto).
  assert (EYX : T1.YX (T4.mg s4) = T1.YX T1.InitialMainGrid)
    by (apply T1P.TypeOKSpec in HT; tauto).
  assert (HR : 0 ≤ T4.pr s4 ≤ 3) by (apply T1P.TypeOKSpec in HT; tauto).
  assert (EYX0 : T1.YX T1.InitialMainGrid = (0, 0))
    by (pose proof T1.AxiomsInitialMainGrid; tauto).
  unfold T1.Y; rewrite EYX, EYX0; split_top; (reflexivity || lia).
Qed.

(* When the game is not over, the piece is Valid where it stands: Valid is
 * the conjunction of the two piece invariants. *)
Lemma PieceValidNow : ∀ [s4 : T4.State]
  (Hc4 : T4.CorrectWithoutGameover s4)
  (Hgo : T4.gameover s4 = false),
  Valid (T4.mg s4) (T4.p s4) (T4.py s4, T4.px s4) (T4.pr s4) = true.
Proof.
  intros.
  assert (Hc1 : T1.CorrectWithoutGameover (T2.s1 (T3.s2 (T4.s3 s4)))) by (
    unfold T4.CorrectWithoutGameover, T3.CorrectWithoutGameover,
      T2.CorrectWithoutGameover in Hc4; tauto).
  unfold T1.CorrectWithoutGameover, T1.PieceOccupiedInsideBounds,
    T1.PieceOnFreeBlocks, T1.PieceGrid in Hc1.
  unfold Valid, T4.py, T4.px, T1.py, T1.px; rewrite <- surjective_pairing.
  rewrite andb_true_iff; tauto.
Qed.

Lemma ShadowYSpecWithoutGameover : ∀ (s4' : T4.State)
  (Hc4 : T4.CorrectWithoutGameover s4')
  (Hgo : T4.gameover s4' = false),
    ShadowY s4' ≤ T4.py s4'
  ∧ Valid (T4.mg s4') (T4.p s4') (ShadowY s4', T4.px s4') (T4.pr s4') = true
  ∧ Valid (T4.mg s4') (T4.p s4') (ShadowY s4' - 1, T4.px s4') (T4.pr s4') = false
  ∧ (∀ y, y ≤ T4.py s4' →
      Valid (T4.mg s4') (T4.p s4') (y, T4.px s4') (T4.pr s4') = true →
      Valid (T4.mg s4') (T4.p s4') (y - 1, T4.px s4') (T4.pr s4') = false →
      y ≤ ShadowY s4').
Proof.
  intros.
  assert (HTY : T1.Y (T4.mg s4') = 0) by (apply T4TypeFacts in Hc4; tauto).
  assert (HR : 0 ≤ T4.pr s4' < 4) by (apply T4TypeFacts in Hc4; tauto).
  assert (HV0 := PieceValidNow Hc4 Hgo).
  assert (HF := ShadowYFuelSufficient (T4.py s4')).
  unfold ShadowY; eapp ShadowYImplSpec.
Qed.

Lemma ShadowYSpec : ∀ (s4' : T4.State)
  (Hc4 : T4.Correct s4')
  (Hgo : T4.gameover s4' = false),
    ShadowY s4' ≤ T4.py s4'
  ∧ Valid (T4.mg s4') (T4.p s4') (ShadowY s4', T4.px s4') (T4.pr s4') = true
  ∧ Valid (T4.mg s4') (T4.p s4') (ShadowY s4' - 1, T4.px s4') (T4.pr s4') = false
  ∧ (∀ y, y ≤ T4.py s4' →
      Valid (T4.mg s4') (T4.p s4') (y, T4.px s4') (T4.pr s4') = true →
      Valid (T4.mg s4') (T4.p s4') (y - 1, T4.px s4') (T4.pr s4') = false →
      y ≤ ShadowY s4').
Proof.
  intros; apply ShadowYSpecWithoutGameover;
    first [ assumption | eapp T4CorrectWithoutGameover ].
Qed.

(* Whether or not the piece is Valid where it stands (i.e. regardless of
 * gameover), the shadow cannot go down: if the search used up its fuel, it
 * went below the floor. *)
Lemma ShadowYAlwaysStops : ∀ (s4 : T4.State)
  (Hc4 : T4.CorrectWithoutGameover s4),
  Valid (T4.mg s4) (T4.p s4) (ShadowY s4 - 1, T4.px s4) (T4.pr s4) = false.
Proof.
  intros.
  assert (HTY : T1.Y (T4.mg s4) = 0) by (apply T4TypeFacts in Hc4; tauto).
  assert (HR : 0 ≤ T4.pr s4 < 4) by (apply T4TypeFacts in Hc4; tauto).
  assert (HF := ShadowYFuelSufficient (T4.py s4)).
  unfold ShadowY; cbv zeta.
  decompose [or] (ShadowYImplStopsOrExhausts (Z.to_nat (T4.py s4) + Z.to_nat PW - 1)
                    (T4.mg s4) (T4.p s4) (T4.py s4) (T4.px s4) (T4.pr s4));
    first [ assumption | apply T1P.ValidBelowFloor; (assumption || lia) ].
Qed.

(* ShadowY is idempotent: recomputing it from a state whose py is already
 * ShadowY s4 (and whose mg/p/pr/px agree with s4) gives back the same value.
 * No gameover hypothesis is needed on either state. *)
Lemma ShadowYIdempotent : ∀ (s4 s4' : T4.State)
  (Hc4 : T4.CorrectWithoutGameover s4)
  (Emg : T4.mg s4' = T4.mg s4)
  (Ep  : T4.p  s4' = T4.p  s4)
  (Epr : T4.pr s4' = T4.pr s4)
  (Epx : T4.px s4' = T4.px s4)
  (Epy : T4.py s4' = ShadowY s4),
  ShadowY s4' = ShadowY s4.
Proof.
  intros; unfold ShadowY at 1; rewrite Emg, Ep, Epr, Epx, Epy.
  apply ShadowYImplNoOpWhenStopped, ShadowYAlwaysStops; assumption.
Qed.

Lemma ShadowYValidOrNoMove : ∀ (s4 : T4.State),
    ShadowY s4 = T4.py s4
  ∨ Valid (T4.mg s4) (T4.p s4) (ShadowY s4, T4.px s4) (T4.pr s4) = true.
Proof. intros; apply ShadowYImplValidOrNoMove. Qed.


(* ========================================================================= *)
(* The T5 invariants follow from the T4 ones and GyEqShadowY                 *)
(* ========================================================================= *)

Lemma GyEqShadowYLowest : ∀ [s : State]
  (Hc4 : T4.CorrectWithoutGameover (s4 s))
  (Hg : GyEqShadowY s),
  LowestShadowY s.
Proof.
  intros; unfold LowestShadowY, ValidPieceCannotGoDown; intros Hgo.
  unfold GyEqShadowY in Hg; rewrite Hg.
  apply ShadowYSpecWithoutGameover in Hgo; try assumption; decompose [and] Hgo.
  repeat split; first [ assumption | intros y Hy [Hv Hv1]; auto ].
Qed.

Lemma LiftCorrectWithoutGameover : ∀ [s : State]
  (Hc4 : T4.CorrectWithoutGameover (s4 s))
  (Hg : GyEqShadowY s),
  CorrectWithoutGameover s.
Proof.
  intros.
  assert (HL : LowestShadowY s) by eapp GyEqShadowYLowest.
  unfold CorrectWithoutGameover; split_top; assumption.
Qed.

Lemma LiftCorrect : ∀ [s : State]
  (Hc4 : T4.Correct (s4 s))
  (Hg : GyEqShadowY s),
  Correct s.
Proof.
  intros.
  assert (HL : LowestShadowY s)
    by (apply GyEqShadowYLowest; first [ assumption | eapp T4CorrectWithoutGameover ]).
  unfold Correct; split_top; assumption.
Qed.


(* ========================================================================= *)
(* Events: what they do to the two components of the state                   *)
(* ========================================================================= *)

Lemma OptionMapSome : ∀ [A B : Type] [f : A → B] [optA : option A] [b : B]
  (H1 : option_map f optA = Some b),
  ∃ a, optA = Some a ∧ f a = b.
Proof. intros; destruct optA as [a |]; [ inject H1; eauto | discriminate H1 ]. Qed.

(* Every T4-forwarded event has the shape `option_map (UpdateShadowY s) o`:
 * the T4 part is the T4 result, and the shadow is recomputed from it. *)
Lemma UpdateShadowYStep : ∀ [s s' : State] [optS4 : option T4.State]
  (Hn : option_map (UpdateShadowY s) optS4 = Some s'),
  ∃ s4', optS4 = Some s4' ∧ s4 s' = s4' ∧ gy s' = ShadowY s4'.
Proof.
  intros s s' [s4' |] Hn; [ inject Hn; subst; exists s4'; now split_top | discriminate Hn ].
Qed.

Lemma UpdateShadowYGuardGyEqShadowY : ∀ [s s' optS4]
  (H1 : option_map (UpdateShadowY s) optS4 = Some s'),
  GyEqShadowY s'.
Proof.
  intros; apply UpdateShadowYStep in H1; unfold GyEqShadowY.
  decompose [ex and] H1; congruence.
Qed.

Lemma NextT4EventUnchangedGy : ∀ [s s' optS4]
  (H1 : gy s = ShadowY (s4 s))
  (H2 : option_map (UpdateShadowY s) optS4 = Some s'),
  gy s' = ShadowY (s4 s').
Proof. intros; eapp UpdateShadowYGuardGyEqShadowY. Qed.

Lemma MovePieceStep : ∀ [s s' : State] [dyx]
  (Hn : MovePiece dyx s = Some s'),
  ∃ s4', T4.MovePiece dyx (s4 s) = Some s4' ∧ s4 s' = s4' ∧ gy s' = ShadowY s4'.
Proof. intros; exact (UpdateShadowYStep Hn). Qed.

Lemma RotatePieceStep : ∀ [s s' : State] [cw]
  (Hn : RotatePiece cw s = Some s'),
  ∃ s4', T4.RotatePiece cw (s4 s) = Some s4' ∧ s4 s' = s4' ∧ gy s' = ShadowY s4'.
Proof. intros; exact (UpdateShadowYStep Hn). Qed.

Lemma FixPieceStep : ∀ [s s' : State] [bagNew] [H : T4.PieceSet bagNew]
  (Hn : FixPiece bagNew H s = Some s'),
  ∃ s4', T4.FixPiece bagNew H (s4 s) = Some s4' ∧ s4 s' = s4' ∧ gy s' = ShadowY s4'.
Proof. intros; exact (UpdateShadowYStep Hn). Qed.

Lemma HoldPieceStep : ∀ [s s' : State] [bagNew] [H : T4.PieceSet bagNew]
  (Hn : HoldPiece bagNew H s = Some s'),
  ∃ s4', T4.HoldPiece bagNew H (s4 s) = Some s4' ∧ s4 s' = s4' ∧ gy s' = ShadowY s4'.
Proof. intros; exact (UpdateShadowYStep Hn). Qed.

Lemma MovePieceFail : ∀ [s : State] [dyx]
  (Hn : MovePiece dyx s = None),
  T4.MovePiece dyx (s4 s) = None.
Proof.
  intros; unfold MovePiece in Hn.
  destruct T4.MovePiece; [ discriminate Hn | reflexivity ].
Qed.

(* Replaces every Move, Rotate, Fix or Hold step hypothesis, and every failed
 * move, by the T4 step it forwards to, in which the new T4 state is written
 * `s4 s'`, and by `gy s' = ShadowY (s4 s')`. *)
Ltac step_facts :=
  repeat match goal with
  | Hm : MovePiece _ _ = Some _ |- _ => apply MovePieceStep in Hm
  | Hm : MovePiece _ _ = None |- _ => apply MovePieceFail in Hm
  | Hm : RotatePiece _ _ = Some _ |- _ => apply RotatePieceStep in Hm
  | Hm : FixPiece _ _ _ = Some _ |- _ => apply FixPieceStep in Hm
  | Hm : HoldPiece _ _ _ = Some _ |- _ => apply HoldPieceStep in Hm
  | H : ∃ _, _ |- _ => destruct H
  | H : _ ∧ _ |- _ => destruct H
  | E : s4 _ = ?s4' |- _ => is_var s4'; subst s4'
  end.

(* A fall step is a move down or, if that fails, a fix. *)
Lemma FallStepCases : ∀ [s s' bagNew] [H : T4.PieceSet bagNew]
  (Hn : FallStep bagNew H s = Some s'),
    MovePiece (-1, 0)%Z s = Some s'
  ∨ (MovePiece (-1, 0)%Z s = None ∧ FixPiece bagNew H s = Some s').
Proof.
  intros; unfold FallStep in Hn.
  destruct MovePiece eqn: Hm; [ inject Hn; subst | ]; tauto.
Qed.

(* T4's fall step takes the same branch. *)
Lemma FallStepStep : ∀ [s s' : State] [bagNew] [H : T4.PieceSet bagNew]
  (Hn : FallStep bagNew H s = Some s'),
  ∃ s4', T4.FallStep bagNew H (s4 s) = Some s4' ∧ s4 s' = s4' ∧ gy s' = ShadowY s4'.
Proof.
  intros; exists (s4 s'); unfold T4.FallStep.
  decompose [or and] (FallStepCases Hn); step_facts;
    match goal with E : T4.MovePiece _ _ = _ |- _ => rewrite E end;
    split_top; (reflexivity || assumption).
Qed.

(* The T4 part of a step on a T4 event is the T4 step. The stutter keeps the
 * shadow, which is therefore up to date only if it was already. *)
Lemma NextT4EventStep : ∀ [e4 : T4.Event] [s s' : State]
  (Hg : GyEqShadowY s)
  (Hn : NextT4Event e4 s = Some s'),
  ∃ s4', T4.Next e4 (s4 s) = Some s4' ∧ s4 s' = s4' ∧ gy s' = ShadowY s4'.
Proof.
  intros; destruct e4; cbn [NextT4Event T4.Next] in *;
    first [ exact (FallStepStep Hn) | exists (s4 s'); step_facts ];
    try match goal with E : Some _ = Some _ |- _ => inject E; subst end;
    split_top; (reflexivity || assumption).
Qed.

(**** What the T4 lemmas give through the s4 projection ****)

(* A successful MovePiece proves T4's own guard held. *)
Lemma MovePieceNotGameover : ∀ [s s' dyx]
  (H1 : MovePiece dyx s = Some s'),
  gameover s = false.
Proof. intros; step_facts; eapp T4P.MovePieceNotGameover. Qed.

(* A successful RotatePiece proves T4's own guard held. *)
Lemma RotatePieceNotGameover : ∀ [s s' cw]
  (H1 : RotatePiece cw s = Some s'),
  gameover s = false.
Proof. intros; step_facts; eapp T4P.RotatePieceNotGameover. Qed.

Lemma HoldPieceNotGameover : ∀ [s s' bagNew H]
  (H1 : HoldPiece bagNew H s = Some s'),
  gameover s = false.
Proof.
  intros.
  assert (E4 : T4.HoldPiece bagNew H (s4 s) = Some (s4 s')) by (step_facts; assumption).
  apply T4P.HoldPieceStep in E4; tauto.
Qed.

Lemma MovePieceMgGameoverUnchanged : ∀ [s s' dyx]
  (Hn : MovePiece dyx s = Some s'),
  mg s' = mg s ∧ gameover s' = gameover s.
Proof. intros; step_facts; eapp T4P.MovePieceMgGameoverUnchanged. Qed.

Lemma RotatePieceMgGameoverUnchanged : ∀ [s s' cw]
  (Hn : RotatePiece cw s = Some s'),
  mg s' = mg s ∧ gameover s' = gameover s.
Proof. intros; step_facts; eapp T4P.RotatePieceMgGameoverUnchanged. Qed.

Lemma HoldPieceMgGameoverUnchanged : ∀ [bagNew] [H : T4.PieceSet bagNew] [s s']
  (Hn : HoldPiece bagNew H s = Some s'),
  mg s' = mg s ∧ gameover s' = gameover s.
Proof. intros; step_facts; eapp T4P.HoldPieceMgGameoverUnchanged. Qed.

(**** Fix, down to T1 ****)

(* A Fix is a T3 Fix of the popped piece, and therefore a T1 Fix. *)
Lemma FixPieceT3 : ∀ [s s' bagNew] [H : T4.PieceSet bagNew]
  (Hn : FixPiece bagNew H s = Some s'),
  T3.FixPiece (T4.next (s4 s) 0) (T4.s3 (s4 s)) = Some (T4.s3 (s4 s')).
Proof.
  intros.
  assert (E4 : T4.FixPiece bagNew H (s4 s) = Some (s4 s')) by (step_facts; assumption).
  apply T4P.FixPieceStep in E4; tauto.
Qed.

Lemma FixPieceT1 : ∀ [s s' bagNew] [H : T4.PieceSet bagNew]
  (Hn : FixPiece bagNew H s = Some s'),
  T1.FixPiece (T4.next (s4 s) 0) (T2.s1 (T3.s2 (T4.s3 (s4 s))))
  = Some (T2.s1 (T3.s2 (T4.s3 (s4 s')))).
Proof.
  intros.
  assert (E2 : T2.FixPiece (T4.next (s4 s) 0) (T3.s2 (T4.s3 (s4 s)))
             = Some (T3.s2 (T4.s3 (s4 s'))))
    by (apply FixPieceT3, T3P.FixPieceStep in Hn; tauto).
  eapp T2P.FixPieceT1.
Qed.

(* A successful FixPiece proves T1's own guard held. *)
Lemma FixPieceNotGameover : ∀ [s s' bagNew H]
  (H1 : FixPiece bagNew H s = Some s'),
  gameover s = false.
Proof.
  intros; apply FixPieceT1 in H1; unfold T1.FixPiece in H1.
  destruct (T1.gameover (T2.s1 (T3.s2 (T4.s3 (s4 s))))) eqn: Ego;
    cbn [negb andb] in H1; first [ discriminate H1 | exact Ego ].
Qed.


(* ========================================================================= *)
(* State invariants                                                          *)
(* ========================================================================= *)

Lemma InitCorrect : ∀ (bags : ℕ → ℕ → Piece) (H : ∀ i, T4.PieceSet (bags i)),
  Correct (Init bags H).
Proof.
  intros.
  assert (HC4 : T4.Correct (s4 (Init bags H))) by apply T4P.InitCorrect.
  assert (HG : GyEqShadowY (Init bags H)) by reflexivity.
  eapp LiftCorrect.
Qed.

(**** CorrectWithoutGameover: the T4 part transfers, the shadow is updated ****)

Lemma MovePieceCorrectWithoutGameover : ∀ [dyx s s']
  (Hc : CorrectWithoutGameover s)
  (Hn : MovePiece dyx s = Some s'),
  CorrectWithoutGameover s'.
Proof.
  intros.
  assert (HC4 : T4.CorrectWithoutGameover (s4 s))
    by (unfold CorrectWithoutGameover in Hc; tauto).
  step_facts.
  assert (HC4' : T4.CorrectWithoutGameover (s4 s'))
    by eapp T4P.MovePieceCorrectWithoutGameover.
  eapp LiftCorrectWithoutGameover.
Qed.

Lemma RotatePieceCorrectWithoutGameover : ∀ [cw s s']
  (Hc : CorrectWithoutGameover s)
  (Hn : RotatePiece cw s = Some s'),
  CorrectWithoutGameover s'.
Proof.
  intros.
  assert (HC4 : T4.CorrectWithoutGameover (s4 s))
    by (unfold CorrectWithoutGameover in Hc; tauto).
  step_facts.
  assert (HC4' : T4.CorrectWithoutGameover (s4 s'))
    by eapp T4P.RotatePieceCorrectWithoutGameover.
  eapp LiftCorrectWithoutGameover.
Qed.

Lemma FixPieceCorrectWithoutGameover : ∀ [bagNew] [H : T4.PieceSet bagNew] [s s']
  (Hc : CorrectWithoutGameover s)
  (Hn : FixPiece bagNew H s = Some s'),
  CorrectWithoutGameover s'.
Proof.
  intros.
  assert (HC4 : T4.CorrectWithoutGameover (s4 s))
    by (unfold CorrectWithoutGameover in Hc; tauto).
  step_facts.
  assert (HC4' : T4.CorrectWithoutGameover (s4 s'))
    by eapp T4P.FixPieceCorrectWithoutGameover.
  eapp LiftCorrectWithoutGameover.
Qed.

(* Hold's weak gameover fact is T4's, through the s4 projection. *)
Lemma HoldPieceCorrectWithoutGameover : ∀ [bagNew] [H : T4.PieceSet bagNew] [s s']
  (Hc : CorrectWithoutGameover s)
  (Hg : ForbiddenGrid ∩ T1.mg (T2.s1 (T3.s2 (T4.s3 (s4 s)))) ⊈ ∅ = true
        → T1.gameover (T2.s1 (T3.s2 (T4.s3 (s4 s)))) = true)
  (Hn : HoldPiece bagNew H s = Some s'),
  CorrectWithoutGameover s'.
Proof.
  intros.
  assert (HC4 : T4.CorrectWithoutGameover (s4 s))
    by (unfold CorrectWithoutGameover in Hc; tauto).
  step_facts.
  assert (HC4' : T4.CorrectWithoutGameover (s4 s'))
    by eapp T4P.HoldPieceCorrectWithoutGameover.
  eapp LiftCorrectWithoutGameover.
Qed.

(**** Correct ****)

Lemma NextT4EventCorrect : ∀ [e4 s s']
  (Hc : Correct s)
  (Hn : NextT4Event e4 s = Some s'),
  Correct s'.
Proof.
  intros.
  assert (HC4 : T4.Correct (s4 s)) by (unfold Correct in Hc; tauto).
  assert (HG : GyEqShadowY s) by (unfold Correct in Hc; tauto).
  apply NextT4EventStep in Hn; try assumption; step_facts.
  assert (HC4' : T4.Correct (s4 s')) by eapp T4P.NextCorrect.
  eapp LiftCorrect.
Qed.

(* Relocating the piece to a Valid position keeps T4.Correct: only the T1
 * part changes, and T1Proofs' NewPieceYXStateCorrect covers it. *)
Lemma NewPieceYXStateCorrect : ∀ [pyx s]
  (HC4 : T4.Correct (s4 s))
  (HV : Valid (mg s) (p s) pyx (pr s) = true),
  T4.Correct (s4 (NewPieceYXState pyx s)).
Proof.
  intros.
  assert (HC1 : T1.Correct (T2.s1 (T3.s2 (T4.s3 (s4 s)))))
    by (unfold T4.Correct, T3.Correct, T2.Correct in HC4; tauto).
  assert (HC1' : T1.Correct (T1.NewPieceYXState pyx (T2.s1 (T3.s2 (T4.s3 (s4 s))))))
    by eapp T1P.NewPieceYXStateCorrect.
  unfold T4.Correct, T3.Correct, T2.Correct in *; cbn; tauto.
Qed.

(* Drop relocates the piece onto its shadow, which LowestShadowY certifies to
 * be Valid since the game is not over (Fix succeeds), then fixes it there. *)
Lemma DropPieceCorrect : ∀ [s s' bagNew] [H : T4.PieceSet bagNew]
  (Hc : Correct s)
  (Hm : DropPiece bagNew H s = Some s'),
  Correct s'.
Proof.
  intros; unfold DropPiece in Hm.
  assert (HC4 : T4.Correct (s4 s)) by (unfold Correct in Hc; tauto).
  assert (HL : LowestShadowY s) by (unfold Correct in Hc; tauto).
  assert (Hgo : gameover s = false) by (apply FixPieceNotGameover in Hm; exact Hm).
  assert (HV : Valid (mg s) (p s) (gy s, px s) (pr s) = true)
    by (unfold LowestShadowY, ValidPieceCannotGoDown in HL; tauto).
  assert (HC4'' : T4.Correct (s4 (NewPieceYXState (gy s, px s) s)))
    by eapp NewPieceYXStateCorrect.
  step_facts.
  assert (HC4' : T4.Correct (s4 s')) by eapp (T4P.NextCorrect (e := T4.Fix bagNew H)).
  eapp LiftCorrect.
Qed.

Lemma NextCorrect : ∀ [e : Event] [s s' : State]
  (Hc : Correct s)
  (Hn : Next e s = Some s'),
  Correct s'.
Proof. intros; destruct e; eauto using NextT4EventCorrect, DropPieceCorrect. Qed.

Theorem SpecCorrect : ∀ e s s',
    (∀ bags H, Correct (Init bags H))
  ∧ (Correct s → Next e s = Some s' → Correct s').
Proof. split_top; eauto using InitCorrect, NextCorrect. Qed.


(* ========================================================================= *)
(* Step invariants                                                           *)
(* ========================================================================= *)

Theorem StepCorrect : ∀ [s] s'
  (Hc : Correct s),
  CorrectStep s s'.
Proof. intros; apply T4P.CorrectStepHold; unfold Correct in Hc; tauto. Qed.

Theorem StepCorrectWithoutGameover : ∀ [s] s'
  (Hc : CorrectWithoutGameover s),
  CorrectStep s s'.
Proof. intros; apply T4P.CorrectStepHoldWithoutGameover; unfold CorrectWithoutGameover in Hc; tauto. Qed.


(* ========================================================================= *)
(* Refinement                                                                *)
(* ========================================================================= *)

Lemma InitRefine : ∀ bags HSet,
  fₛ (Init bags HSet) = T4.Init bags HSet.
Proof. reflexivity. Qed.

(*
         e4
   s4    →    s4'
fₛ ↑     ⇑fₑ  ↑ fₛ
   s5    →    s5'
         e5
*)

Lemma NextRefine : ∀ e4 s5 s5'
  (H1 : GyEqShadowY s5)
  (H2 : NextT4Event e4 s5 = Some s5'),
  T4.Next (fₑ e4) (fₛ s5) = Some (fₛ s5').
Proof. intros; apply NextT4EventStep in H2; step_facts; assumption. Qed.

Theorem T4RefinesT5Hold : T4RefinesT5.
Proof. unfold T4RefinesT5; split_top; auto using InitRefine, NextRefine. Qed.


(* ========================================================================= *)
(* Helpers for refining models                                               *)
(* ========================================================================= *)

Lemma MovePieceUnchangedGameover : ∀ [s s' dyx]
  (H1 : MovePiece dyx s = Some s'),
  gameover s' = gameover s.
Proof. intros; apply MovePieceMgGameoverUnchanged in H1; tauto. Qed.

Lemma RotatePieceUnchangedGameover : ∀ [s s' cw]
  (H1 : RotatePiece cw s = Some s'),
  gameover s' = gameover s.
Proof. intros; apply RotatePieceMgGameoverUnchanged in H1; tauto. Qed.

(* After a Fix, the new piece is at its initial position and rotation. *)
Lemma FixPieceFreshPiece : ∀ [s s' bagNew] [H : T4.PieceSet bagNew]
  (Hn : FixPiece bagNew H s = Some s'),
  ∃ pNew,
    T1.p (T2.s1 (T3.s2 (T4.s3 (s4 s')))) = pNew
  ∧ T1.pyx (T2.s1 (T3.s2 (T4.s3 (s4 s')))) = T1.InitialYX pNew
  ∧ T1.pr (T2.s1 (T3.s2 (T4.s3 (s4 s')))) = 0.
Proof.
  intros; apply FixPieceT1, T1P.FixPieceOK in Hn.
  exists (T4.next (s4 s) 0); split_top; tauto.
Qed.

(* After a Fix, gameover is exactly the forbidden zone meeting the grid. *)
Lemma FixPieceGameoverEq : ∀ [bagNew] [H : T4.PieceSet bagNew] [s s' : State]
  (Hn : FixPiece bagNew H s = Some s'),
  gameover s' = (ForbiddenGrid ∩ mg s' ⊈ ∅).
Proof. intros; apply FixPieceT1, T1P.FixPieceOK in Hn; tauto. Qed.

(* A Fix always resets `swapped`. *)
Lemma FixPieceSwappedFalse : ∀ [bagNew] [H : T4.PieceSet bagNew] [s s' : State]
  (Hn : FixPiece bagNew H s = Some s'),
  T3.swapped (T4.s3 (s4 s')) = false.
Proof. intros; apply FixPieceT3, T3P.FixPieceStep in Hn; tauto. Qed.
