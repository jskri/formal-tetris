From Tetris Require Import T2 Notations.
From Tetris Require T1Proofs.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import T1(ForbiddenGrid).
Import (notations) T1.
Import ListNotations.

Open Scope nat_scope.

Module T1P := T1Proofs.

(* ========================================================================= *)
(* Events: what they change                                                  *)
(* ========================================================================= *)

(* Move and Rotate update the T1 part only, through UpdateS1. *)
Lemma UpdateS1Step : ∀ [o s s']
  (Hn : UpdateS1 o s = Some s'),
    Some (s1 s') = o
  ∧ score s' = score s
  ∧ level s' = level s
  ∧ combo s' = combo s
  ∧ perfectClear s' = perfectClear s
  ∧ totalClearedLines s' = totalClearedLines s.
Proof.
  intros [t |] s s' Hn; [ inject Hn; subst; now split_top | discriminate Hn ].
Qed.

Lemma MovePieceStep : ∀ [s s' dyx]
    (Hn : MovePiece dyx s = Some s'),
    Some (s1 s') = T1.MovePiece dyx (s1 s)
  ∧ score s' = score s
  ∧ level s' = level s
  ∧ combo s' = combo s
  ∧ perfectClear s' = perfectClear s
  ∧ totalClearedLines s' = totalClearedLines s.
Proof. intros; apply UpdateS1Step in Hn; split_top; tauto. Qed.

Lemma RotatePieceStep : ∀ [s s' cw]
  (Hn : RotatePiece cw s = Some s'),
    Some (s1 s') = T1.RotatePiece cw (s1 s)
  ∧ score s' = score s
  ∧ level s' = level s
  ∧ combo s' = combo s
  ∧ perfectClear s' = perfectClear s
  ∧ totalClearedLines s' = totalClearedLines s.
Proof. intros; apply UpdateS1Step in Hn; split_top; tauto. Qed.

Lemma FixPieceStep : ∀ [s s' p_new]
  (Hn : FixPiece p_new s = Some s'),
  let s1' := s1 s' in
  let clearedLines := clearedLines s1' in
  let combo' := (if clearedLines =? 0 then 0 else combo s + 1) in
  let perfectClear' := EmptyGridb (mg s') in
  let totalClearedLines' := totalClearedLines s + clearedLines in
    Some s1' = T1.FixPiece p_new (s1 s)
  ∧ score s' = score s + (Points clearedLines (level s) (combo'-1) perfectClear')
  ∧ level s' = 1 + totalClearedLines' / 10
  ∧ combo s' = combo'
  ∧ perfectClear s' = perfectClear'
  ∧ totalClearedLines s' = totalClearedLines'.
Proof.
  intros s s' p_new Hn; unfold FixPiece in Hn.
  destruct T1.FixPiece; [ inject Hn; subst; now split_top | discriminate Hn ].
Qed.

(* The T1 part of a successful T2 step is the result of the T1 step. *)
Lemma MovePieceT1 : ∀ [s s' dyx]
  (Hn : MovePiece dyx s = Some s'),
  T1.MovePiece dyx (s1 s) = Some (s1 s').
Proof. intros; symmetry; apply MovePieceStep in Hn; tauto. Qed.

Lemma RotatePieceT1 : ∀ [s s' cw]
  (Hn : RotatePiece cw s = Some s'),
  T1.RotatePiece cw (s1 s) = Some (s1 s').
Proof. intros; symmetry; apply RotatePieceStep in Hn; tauto. Qed.

Lemma FixPieceT1 : ∀ [s s' p_new]
  (Hn : FixPiece p_new s = Some s'),
  T1.FixPiece p_new (s1 s) = Some (s1 s').
Proof. intros; symmetry; apply FixPieceStep in Hn; cbv zeta in Hn; tauto. Qed.

(* All T2 step functions are T1 ones, mapped over: they fail when T1's do. *)
Lemma OptionMapNone : ∀ [A B] [f : A → B] [o]
  (Hn : option_map f o = None),
  o = None.
Proof. intros A B f [] Hn; easy. Qed.

(* A fall step is a move down or, if that fails, a fix. *)
Lemma FallStepCases : ∀ [s s' p_new]
  (Hn : FallStep p_new s = Some s'),
    MovePiece (-1, 0)%Z s = Some s'
  ∨ (MovePiece (-1, 0)%Z s = None ∧ FixPiece p_new s = Some s').
Proof.
  intros; unfold FallStep in Hn.
  destruct MovePiece eqn: Hm; [ inject Hn; subst | ]; tauto.
Qed.

Lemma FallStepT1 : ∀ [s s' p_new]
  (Hn : FallStep p_new s = Some s'),
  T1.FallStep p_new (s1 s) = Some (s1 s').
Proof.
  intros; unfold T1.FallStep.
  decompose [or and] (FallStepCases Hn);
    match goal with
    | Hm : MovePiece _ _ = Some _ |- _ => rewrite (MovePieceT1 Hm); reflexivity
    | Hm : MovePiece _ _ = None |- _ =>
        (* T2's move down failed, hence so did T1's *)
        rewrite (OptionMapNone Hm); eapp FixPieceT1
    end.
Qed.

Lemma FallStepNone : ∀ [s p_new]
  (Hn : FallStep p_new s = None),
  T1.FallStep p_new (s1 s) = None.
Proof.
  intros; unfold FallStep, T1.FallStep in *.
  destruct MovePiece eqn: Hm in Hn; [ discriminate Hn | ].
  rewrite (OptionMapNone Hm); exact (OptionMapNone Hn).
Qed.

(* Every successful step is a move, a rotation, a fix or a stutter. *)
Lemma NextCases : ∀ [e s s']
  (Hn : Next e s = Some s'),
    (∃ dyx, MovePiece dyx s = Some s')
  ∨ (∃ cw, RotatePiece cw s = Some s')
  ∨ (∃ p_new, FixPiece p_new s = Some s')
  ∨ s' = s.
Proof.
  intros; destruct e; cbn [Next] in Hn;
    try (decompose [or and] (FallStepCases Hn); clear Hn);
    try (inject Hn; subst);
    eauto 6.
Qed.

(* A successful MovePiece proves T1's own guard held. *)
Lemma MovePieceNotGameover : ∀ [s s' dyx]
  (H1 : MovePiece dyx s = Some s'),
  gameover s = false.
Proof.
  intros.
  assert (E1 : T1.MovePiece dyx (s1 s) = Some (s1 s')) by eapp MovePieceT1.
  eapp T1P.MovePieceNotGameover.
Qed.

(* A successful RotatePiece proves T1's own guard held. *)
Lemma RotatePieceNotGameover : ∀ [s s' cw]
  (H1 : RotatePiece cw s = Some s'),
  gameover s = false.
Proof.
  intros.
  assert (E1 : T1.RotatePiece cw (s1 s) = Some (s1 s')) by eapp RotatePieceT1.
  eapp T1P.RotatePieceNotGameover.
Qed.

(* mg and gameover are both literally unchanged across Move/Rotate at T1, so
they carry over unchanged here too. Needed (not by CorrectWithoutGameover
itself, which doesn't care what mg/gameover actually are) for transferring
the weak Gameover fact across a step at the T7 level. *)
Lemma MovePieceMgGameoverUnchanged : ∀ [s s' dyx]
  (Hn : MovePiece dyx s = Some s'),
  mg s' = mg s ∧ gameover s' = gameover s.
Proof.
  intros.
  assert (E1 : T1.MovePiece dyx (s1 s) = Some (s1 s')) by eapp MovePieceT1.
  assert (Emg : T1.mg (s1 s') = T1.mg (s1 s))
    by (apply T1P.MovePieceUnchanged in E1; tauto).
  assert (Ego : T1.gameover (s1 s') = T1.gameover (s1 s))
    by (apply T1P.MovePieceUnchanged in E1; tauto).
  split_top; assumption.
Qed.

Lemma RotatePieceMgGameoverUnchanged : ∀ [s s' cw]
  (Hn : RotatePiece cw s = Some s'),
  mg s' = mg s ∧ gameover s' = gameover s.
Proof.
  intros.
  assert (E1 : T1.RotatePiece cw (s1 s) = Some (s1 s')) by eapp RotatePieceT1.
  assert (Emg : T1.mg (s1 s') = T1.mg (s1 s))
    by (apply T1P.RotatePieceOK in E1; tauto).
  assert (Ego : T1.gameover (s1 s') = T1.gameover (s1 s))
    by (apply T1P.RotatePieceOK in E1; tauto).
  split_top; assumption.
Qed.


(* ========================================================================= *)
(* State invariants                                                          *)
(* ========================================================================= *)

(* LevelCorrect only reads level and totalClearedLines. *)
Lemma LevelCorrectUnchanged : ∀ [s s']
  (El : level s' = level s)
  (Et : totalClearedLines s' = totalClearedLines s)
  (Hl : LevelCorrect s),
  LevelCorrect s'.
Proof. unfold LevelCorrect; congruence. Qed.

(* Move and Rotate leave level and totalClearedLines unchanged. *)
Lemma MovePieceLevelCorrect : ∀ [s s' dyx]
  (Hl : LevelCorrect s)
  (Hn : MovePiece dyx s = Some s'),
  LevelCorrect s'.
Proof.
  intros.
  assert (El : level s' = level s) by (apply MovePieceStep in Hn; tauto).
  assert (Et : totalClearedLines s' = totalClearedLines s)
    by (apply MovePieceStep in Hn; tauto).
  eapp LevelCorrectUnchanged.
Qed.

Lemma RotatePieceLevelCorrect : ∀ [s s' cw]
  (Hl : LevelCorrect s)
  (Hn : RotatePiece cw s = Some s'),
  LevelCorrect s'.
Proof.
  intros.
  assert (El : level s' = level s) by (apply RotatePieceStep in Hn; tauto).
  assert (Et : totalClearedLines s' = totalClearedLines s)
    by (apply RotatePieceStep in Hn; tauto).
  eapp LevelCorrectUnchanged.
Qed.

(* FixPiece recomputes the level from totalClearedLines: LevelCorrect holds
 * afterwards, whatever held before. *)
Lemma FixPieceLevelCorrect : ∀ [s s' p_new]
  (Hn : FixPiece p_new s = Some s'),
  LevelCorrect s'.
Proof.
  intros.
  assert (El : level s' = 1 + (totalClearedLines s + clearedLines (s1 s')) / 10)
    by (apply FixPieceStep in Hn; cbv zeta in Hn; tauto).
  assert (Et : totalClearedLines s' = totalClearedLines s + clearedLines (s1 s'))
    by (apply FixPieceStep in Hn; cbv zeta in Hn; tauto).
  unfold LevelCorrect; congruence.
Qed.

Lemma InitCorrect : ∀ p : Piece, Correct (Init p).
Proof.
  intros.
  assert (HC1 : T1.Correct (s1 (Init p))) by apply T1P.InitCorrect.
  assert (Hl : LevelCorrect (Init p)) by reflexivity.
  unfold Correct; split_top; assumption.
Qed.

(**** CorrectWithoutGameover: the T1 part transfers, then LevelCorrect ****)

Lemma MovePieceCorrectWithoutGameover : ∀ [dyx s s']
  (Hc : CorrectWithoutGameover s)
  (Hn : MovePiece dyx s = Some s'),
  CorrectWithoutGameover s'.
Proof.
  intros.
  assert (HC1 : T1.CorrectWithoutGameover (s1 s))
    by (unfold CorrectWithoutGameover in Hc; tauto).
  assert (Hl : LevelCorrect s) by (unfold CorrectWithoutGameover in Hc; tauto).
  assert (E1 : T1.MovePiece dyx (s1 s) = Some (s1 s')) by eapp MovePieceT1.
  assert (HC1' : T1.CorrectWithoutGameover (s1 s'))
    by eapp T1P.MovePieceCorrectWithoutGameover.
  assert (Hl' : LevelCorrect s') by eapp MovePieceLevelCorrect.
  unfold CorrectWithoutGameover; split_top; assumption.
Qed.

Lemma RotatePieceCorrectWithoutGameover : ∀ [cw s s']
  (Hc : CorrectWithoutGameover s)
  (Hn : RotatePiece cw s = Some s'),
  CorrectWithoutGameover s'.
Proof.
  intros.
  assert (HC1 : T1.CorrectWithoutGameover (s1 s))
    by (unfold CorrectWithoutGameover in Hc; tauto).
  assert (Hl : LevelCorrect s) by (unfold CorrectWithoutGameover in Hc; tauto).
  assert (E1 : T1.RotatePiece cw (s1 s) = Some (s1 s')) by eapp RotatePieceT1.
  assert (HC1' : T1.CorrectWithoutGameover (s1 s'))
    by eapp T1P.RotatePieceCorrectWithoutGameover.
  assert (Hl' : LevelCorrect s') by eapp RotatePieceLevelCorrect.
  unfold CorrectWithoutGameover; split_top; assumption.
Qed.

Lemma FixPieceCorrectWithoutGameover : ∀ [p_new s s']
  (Hc : CorrectWithoutGameover s)
  (Hn : FixPiece p_new s = Some s'),
  CorrectWithoutGameover s'.
Proof.
  intros.
  assert (HC1 : T1.CorrectWithoutGameover (s1 s))
    by (unfold CorrectWithoutGameover in Hc; tauto).
  assert (E1 : T1.FixPiece p_new (s1 s) = Some (s1 s')) by eapp FixPieceT1.
  assert (HC1' : T1.CorrectWithoutGameover (s1 s'))
    by eapp T1P.FixPieceCorrectWithoutGameover.
  assert (Hl' : LevelCorrect s') by eapp FixPieceLevelCorrect.
  unfold CorrectWithoutGameover; split_top; assumption.
Qed.

(* Used by T3's HoldPiece; needs the weak gameover fact about s1 s to thread
into T1P.NewPieceStateCorrectWithoutGameover. *)
Lemma NewPieceStateCorrectWithoutGameover : ∀ (p_new : Piece) (s : State)
  (Hc : CorrectWithoutGameover s)
  (Hg : ForbiddenGrid ∩ T1.mg (s1 s) ⊈ ∅ = true → T1.gameover (s1 s) = true),
  CorrectWithoutGameover (UnchangedT2Part s (T1.NewPieceState p_new (s1 s))).
Proof.
  intros.
  assert (HC1 : T1.CorrectWithoutGameover (s1 s))
    by (unfold CorrectWithoutGameover in Hc; tauto).
  assert (Hl : LevelCorrect s) by (unfold CorrectWithoutGameover in Hc; tauto).
  assert (HC1' : T1.CorrectWithoutGameover (T1.NewPieceState p_new (s1 s)))
    by (apply T1P.NewPieceStateCorrectWithoutGameover; assumption).
  (* level and totalClearedLines are copied verbatim by UnchangedT2Part *)
  unfold CorrectWithoutGameover; split_top; assumption.
Qed.

(**** Correct: same structure ****)

Lemma MovePieceCorrect : ∀ [dyx s s']
  (Hc : Correct s)
  (Hn : MovePiece dyx s = Some s'),
  Correct s'.
Proof.
  intros.
  assert (HC1 : T1.Correct (s1 s)) by (unfold Correct in Hc; tauto).
  assert (Hl : LevelCorrect s) by (unfold Correct in Hc; tauto).
  assert (E1 : T1.MovePiece dyx (s1 s) = Some (s1 s')) by eapp MovePieceT1.
  assert (HC1' : T1.Correct (s1 s')) by eapp T1P.MovePieceCorrect.
  assert (Hl' : LevelCorrect s') by eapp MovePieceLevelCorrect.
  unfold Correct; split_top; assumption.
Qed.

Lemma RotatePieceCorrect : ∀ [cw s s']
  (Hc : Correct s)
  (Hn : RotatePiece cw s = Some s'),
  Correct s'.
Proof.
  intros.
  assert (HC1 : T1.Correct (s1 s)) by (unfold Correct in Hc; tauto).
  assert (Hl : LevelCorrect s) by (unfold Correct in Hc; tauto).
  assert (E1 : T1.RotatePiece cw (s1 s) = Some (s1 s')) by eapp RotatePieceT1.
  assert (HC1' : T1.Correct (s1 s')) by eapp T1P.RotatePieceCorrect.
  assert (Hl' : LevelCorrect s') by eapp RotatePieceLevelCorrect.
  unfold Correct; split_top; assumption.
Qed.

Lemma FixPieceCorrect : ∀ [p_new s s']
  (Hc : Correct s)
  (Hn : FixPiece p_new s = Some s'),
  Correct s'.
Proof.
  intros.
  assert (HC1 : T1.Correct (s1 s)) by (unfold Correct in Hc; tauto).
  assert (E1 : T1.FixPiece p_new (s1 s) = Some (s1 s')) by eapp FixPieceT1.
  assert (HC1' : T1.Correct (s1 s')) by eapp T1P.FixPieceCorrect.
  assert (Hl' : LevelCorrect s') by eapp FixPieceLevelCorrect.
  unfold Correct; split_top; assumption.
Qed.

Lemma NextCorrect : ∀ [e s s']
  (Hc : Correct s)
  (He : Next e s = Some s'),
  Correct s'.
Proof.
  intros.
  decompose [or ex] (NextCases He); subst;
    eauto using MovePieceCorrect, RotatePieceCorrect, FixPieceCorrect.
Qed.

Theorem SpecCorrect : ∀ e s s',
    (∀ p, Correct (Init p))
  ∧ (Correct s → Next e s = Some s' → Correct s').
Proof. split_top; eauto using InitCorrect, NextCorrect. Qed.


(* ========================================================================= *)
(* Step invariants                                                           *)
(* ========================================================================= *)

(* Move, Rotate and Stutter leave score and totalClearedLines unchanged; Fix
 * adds to both. *)
Lemma NextNonDecreasing : ∀ [e s s']
  (Hn : Next e s = Some s'),
  score s <= score s' ∧ totalClearedLines s <= totalClearedLines s'.
Proof.
  intros.
  decompose [or ex] (NextCases Hn); subst;
    repeat match goal with
    | Hm : MovePiece _ _ = Some _ |- _ => apply MovePieceStep in Hm
    | Hm : RotatePiece _ _ = Some _ |- _ => apply RotatePieceStep in Hm
    | Hm : FixPiece _ _ = Some _ |- _ => apply FixPieceStep in Hm; cbv zeta in Hm
    end;
    lia.
Qed.

Theorem StepNonDecreasingScore : ∀ s s',
  NonDecreasingScore s s'.
Proof. intros s s' e Hn; apply NextNonDecreasing in Hn; tauto. Qed.

Theorem StepNonDecreasingTotalClearedLines : ∀ [s s' e]
  (Hn : Next e s = Some s'),
  totalClearedLines s <= totalClearedLines s'.
Proof. intros; apply NextNonDecreasing in Hn; tauto. Qed.

Theorem StepNonDecreasingLevel : ∀ [s] s'
  (Hc : Correct s),
  NonDecreasingLevel s s'.
Proof.
  intros s s' Hc e Hn.
  (* level is a monotone function of totalClearedLines on Correct states *)
  assert (Hc' : Correct s') by eapp NextCorrect.
  assert (Hl : LevelCorrect s) by (unfold Correct in Hc; tauto).
  assert (Hl' : LevelCorrect s') by (unfold Correct in Hc'; tauto).
  assert (Ht : totalClearedLines s <= totalClearedLines s')
    by eapp StepNonDecreasingTotalClearedLines.
  unfold LevelCorrect in Hl, Hl'; rewrite Hl, Hl'.
  pose proof (Nat.Div0.div_le_mono _ _ 10 Ht); lia.
Qed.

(* Clearing at least one line, at a positive level, earns points. *)
Lemma PointsPositive : ∀ clearedLines level combo perfectClear
  (Hi : 0 < clearedLines)
  (Hv : 0 < level),
  0 < Points clearedLines level combo perfectClear.
Proof.
  intros [| [| [| [| n]]]] level combo perfectClear Hi Hv;
    unfold Points; cbn [LineClearPoints]; lia.
Qed.

Theorem StepScoreRisesOnClear (s s' : State) :
  ScoreRisesOnClear s s'.
Proof.
  intros p_new Hc Hn Hcl.
  (* LevelCorrect s makes the level positive *)
  assert (Hl : LevelCorrect s) by (unfold Correct in Hc; tauto).
  assert (Hv : 0 < level s) by (unfold LevelCorrect in Hl; lia).
  set (cl := clearedLines (s1 s')) in *.
  set (combo' := (if cl =? 0 then 0 else combo s + 1) - 1).
  set (pc := EmptyGridb (mg s')).
  assert (Esc : score s' = score s + Points cl (level s) combo' pc)
    by (apply FixPieceStep in Hn; cbv zeta in Hn; tauto).
  assert (HP : 0 < Points cl (level s) combo' pc) by (apply PointsPositive; assumption).
  lia.
Qed.

(* NonDecreasingLevel is the only conjunct needing `Correct s`: FixPiece resets
 * level to `1 + totalClearedLines'/10`, which is below an arbitrary `level s`
 * unless LevelCorrect holds. *)
Theorem CorrectStepHold : ∀ [s] s'
  (Hc : Correct s),
  CorrectStep s s'.
Proof.
  intros; unfold CorrectStep; split_top; auto using StepNonDecreasingScore,
    StepNonDecreasingLevel, StepScoreRisesOnClear.
Qed.


(* ========================================================================= *)
(* Refinement                                                                *)
(* ========================================================================= *)

(***************)
(* T2RefinesT1 *)
(***************)

Lemma RefineInit : ∀ p, fₛ (T2.Init p) = T1.Init p.
Proof. reflexivity. Qed.

(*
         e1
   s1    →    s1'
fₛ ↑     ⇑fₑ  ↑ fₛ
   s2    →    s2'
         e2
*)

Lemma RefineNext : ∀ [s2 s2' e2]
  (Hn : T2.Next e2 s2 = Some s2'),
  T1.Next (fₑ e2) (fₛ s2) = Some (fₛ s2').
Proof.
  intros; destruct e2; unfold fₛ; cbn [Next T1.Next fₑ] in *;
    first [ congruence | eauto using MovePieceT1, RotatePieceT1, FixPieceT1, FallStepT1 ].
Qed.

(* Conversely, a T2 step fails only when its T1 counterpart does: both
 * steps are guarded by the same T1 step functions. *)
Lemma RefineNextNone : ∀ [s2 e2]
  (Hn : T2.Next e2 s2 = None),
  T1.Next (fₑ e2) (fₛ s2) = None.
Proof.
  intros; destruct e2; unfold fₛ; cbn [Next T1.Next fₑ] in *;
    first [ discriminate Hn | exact (OptionMapNone Hn) | eapp FallStepNone ].
Qed.

Theorem SpecRefine : T2RefinesT1.
Proof. unfold T2RefinesT1; split_top; auto using RefineInit, RefineNext. Qed.


(*****************)
(* T2AllowsAllT1 *)
(*****************)

(*
               es1
   T1.Init p   →         s1'
fₛ ↑           ⇓ map gₑ  ↑ fₛ
   T2.Init p   →         s2'
               es2
*)

Lemma feRetractsGe : ∀ e1, fₑ (gₑ e1) = e1.
Proof. destruct e1; now simpl. Qed.

Lemma StepLifts :
  ∀ [e1 s1 s1' s2]
    (H1 : fₛ s2 = s1)
    (H2 : T1.Next e1 s1 = Some s1'),
    ∃ s2', T2.Next (gₑ e1) s2 = Some s2' ∧ fₛ s2' = s1'.
Proof.
  intros.
  destruct (T2.Next (gₑ e1) s2) as [s2' |] eqn: Hn.
  - assert (Hfs : fₛ s2' = s1')
      by (apply RefineNext in Hn; rewrite feRetractsGe, H1, H2 in Hn; congruence).
    exists s2'; split_top; (reflexivity || assumption).
  - apply RefineNextNone in Hn; rewrite feRetractsGe, H1, H2 in Hn; discriminate Hn.
Qed.

(* Generalized over the starting states, so that the induction hypothesis
 * applies at every point along the run. *)
Lemma RunLifts : ∀ es1 s1 s1' s2
  (Hfs : fₛ s2 = s1)
  (Hrun : RunT1 es1 s1 = Some s1'),
  ∃ s2', RunT2 (map gₑ es1) s2 = Some s2' ∧ fₛ s2' = s1'.
Proof.
  induction es1 as [| e1 es1 IH]; intros; cbn [RunT1 RunT2 map] in Hrun |- *.
  - exists s2; split_top; congruence.
  - destruct (T1.Next e1 s1) as [s1'' |] eqn: Hstep; [ | discriminate Hrun ].
    (* the T1 step lifts to a T2 step from s2, then the induction hypothesis
     * lifts the rest of the run *)
    apply StepLifts with (s2 := s2) in Hstep; [ | assumption ].
    destruct Hstep as (s2'' & Hstep).
    assert (Hn : T2.Next (gₑ e1) s2 = Some s2'') by tauto.
    assert (Hfs'' : fₛ s2'' = s1'') by tauto.
    rewrite Hn; eapp IH.
Qed.

Theorem T2AllowsAllT1Hold : T2AllowsAllT1.
Proof.
  intros p es1 s1' H1.
  assert (HI : fₛ (T2.Init p) = T1.Init p) by apply RefineInit.
  apply RunLifts with (s2 := T2.Init p) in H1; [ | assumption ].
  destruct H1 as (s2' & H1); exists s2'; split_top; tauto.
Qed.


(* ========================================================================= *)
(* Helpers for refining models                                               *)
(* ========================================================================= *)

(* Spawning a new current piece leaves score, level, combo, perfectClear and
 * totalClearedLines untouched, so T2's own invariant reduces to T1's. Used by
 * T3's HoldPiece. *)
Lemma NewPieceStateCorrect : ∀ (p_new : Piece) (s : State)
  (Hc : Correct s),
  Correct (UnchangedT2Part s (T1.NewPieceState p_new (s1 s))).
Proof.
  intros.
  assert (HC1 : T1.Correct (s1 s)) by (unfold Correct in Hc; tauto).
  assert (Hl : LevelCorrect s) by (unfold Correct in Hc; tauto).
  assert (HC1' : T1.Correct (T1.NewPieceState p_new (s1 s)))
    by (apply T1P.NewPieceStateCorrect; assumption).
  (* level and totalClearedLines are copied verbatim by UnchangedT2Part *)
  unfold Correct; split_top; assumption.
Qed.
