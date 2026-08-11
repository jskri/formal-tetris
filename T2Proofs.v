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
(* Helpers                                                                   *)
(* ========================================================================= *)

Lemma MovePieceStep : ∀ [s s' dyx]
    (Hn : MovePiece dyx s = Some s'),
    Some (s1 s') = T1.MovePiece dyx (s1 s)
  ∧ score s' = score s
  ∧ level s' = level s
  ∧ combo s' = combo s
  ∧ perfectClear s' = perfectClear s
  ∧ totalClearedLines s' = totalClearedLines s.
Proof.
  intros.
  unfold MovePiece, UpdateS1, option_map in Hn.
  destruct T1.MovePiece as [t |] eqn: Hd in Hn.
  - assert (L1 : s' = {|s1 := t; score := score s; level := level s; combo := combo s;
        perfectClear := perfectClear s; totalClearedLines := totalClearedLines s|})
      by now inject Hn.
    assert (L2 : Some (s1 s') = T1.MovePiece dyx (s1 s))
      by now rewrite L1, Hd; reflexivity.
    assert (L3 : score s' = score s ∧ level s' = level s ∧ combo s' = combo s ∧
        perfectClear s' = perfectClear s ∧ totalClearedLines s' = totalClearedLines s). {
      rewrite L1. repeat split; reflexivity.
    }
    split; auto using L2, L3.
  - discriminate Hn.
Qed.

Lemma MovePieceFail : ∀ [s dy dx]
  (Hn : MovePiece (dy, dx) s = None),
  T1.MovePiece (dy, dx) (s1 s) = None.
Proof.
  intros.
  unfold MovePiece, UpdateS1, option_map in Hn.
  destruct T1.MovePiece eqn: H1 in Hn.
  - discriminate Hn.
  - congruence.
Qed.

Lemma RotatePieceStep : ∀ [s s' cw]
  (Hn : RotatePiece cw s = Some s'),
    Some (s1 s') = T1.RotatePiece cw (s1 s)
  ∧ score s' = score s
  ∧ level s' = level s
  ∧ combo s' = combo s
  ∧ perfectClear s' = perfectClear s
  ∧ totalClearedLines s' = totalClearedLines s.
Proof.
  intros.
  unfold RotatePiece, UpdateS1, option_map in Hn.
  destruct T1.RotatePiece as [t |] eqn: Hd in Hn.
  - assert (L1 : s' = {|s1 := t; score := score s; level := level s; combo := combo s;
        perfectClear := perfectClear s; totalClearedLines := totalClearedLines s|})
      by now inject Hn.
    assert (L2 : Some (s1 s') = T1.RotatePiece cw (s1 s))
      by now rewrite L1, Hd; reflexivity.
    assert (L3 : score s' = score s ∧ level s' = level s ∧ combo s' = combo s ∧
        perfectClear s' = perfectClear s ∧ totalClearedLines s' = totalClearedLines s). {
      rewrite L1. repeat split; reflexivity.
    }
    split; auto using L2, L3.
  - discriminate Hn.
Qed.

(* A successful MovePiece proves T1's own guard held. *)
Lemma MovePieceNotGameover : ∀ [s s' dyx]
  (H1 : MovePiece dyx s = Some s'),
  gameover s = false.
Proof.
  intros.
  destruct (MovePieceStep H1) as [H2 _].
  exact (T1P.MovePieceNotGameover (eq_sym H2)).
Qed.

(* A successful RotatePiece proves T1's own guard held. *)
Lemma RotatePieceNotGameover : ∀ [s s' cw]
  (H1 : RotatePiece cw s = Some s'),
  gameover s = false.
Proof.
  intros.
  destruct (RotatePieceStep H1) as [H2 _].
  exact (T1P.RotatePieceNotGameover (eq_sym H2)).
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
  destruct (MovePieceStep Hn) as [H2 _].
  destruct (T1P.MovePieceUnchanged dyx (s1 s) (s1 s') (eq_sym H2)) as (Emg & _ & _ & Ego).
  split; [exact Emg | exact Ego].
Qed.

Lemma RotatePieceMgGameoverUnchanged : ∀ [s s' cw]
  (Hn : RotatePiece cw s = Some s'),
  mg s' = mg s ∧ gameover s' = gameover s.
Proof.
  intros.
  destruct (RotatePieceStep Hn) as [H2 _].
  destruct (T1P.RotatePieceOK cw (s1 s) (s1 s') (eq_sym H2)) as (Emg & _ & _ & Ego & _).
  split; [exact Emg | exact Ego].
Qed.

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
  intros.
  unfold FixPiece, UpdateS1, option_map in Hn.
  destruct T1.FixPiece as [t |] eqn: Hd in Hn.
  - inject Hn.
    assert (L2 : Some s1' = T1.FixPiece p_new (s1 s))
      by now unfold s1'; rewrite <- Hn, Hd; reflexivity.
    assert (L3 : score s' = score s + (Points clearedLines (level s) (combo'-1) perfectClear')
        ∧ level s' = 1 + totalClearedLines' / 10
        ∧ combo s' = combo'
        ∧ perfectClear s' = perfectClear'
        ∧ totalClearedLines s' = totalClearedLines'). {
      rewrite <- Hn.
      (let finish clearedLines combo' perfectClear' totalClearedLines' s1' H := (
        unfold clearedLines, combo', perfectClear', totalClearedLines'; 
        unfold clearedLines, s1';
        rewrite <- H;
        reflexivity) in
      repeat split; now finish clearedLines combo' perfectClear' totalClearedLines' s1' Hn).
    }
    split; auto using L2, L3.
  - discriminate Hn.
Qed.

Lemma StutterStep : ∀ [s s']
  (Hn : Next Stutter s = Some s'),
  s' = s.
Proof.
  intros.
  simpl in Hn.
  now inject Hn.
Qed.


(* ========================================================================= *)
(* State invariants                                                          *)
(* ========================================================================= *)

Lemma InitCorrect : ∀ p : Piece, Correct (Init p).
Proof.
  intros.
  set (s := Init p).
  assert (L1 : T1.Correct (s1 s)) by now apply T1P.InitCorrect.
  assert (L2 : LevelCorrect s) by now unfold LevelCorrect; simpl; lia.
  split; auto using L1, L2.
Qed.

Lemma MovePieceCorrectWithoutGameover : ∀ [dyx s s']
  (Hc : CorrectWithoutGameover s)
  (Hn : MovePiece dyx s = Some s'),
  CorrectWithoutGameover s'.
Proof.
  intros.
  apply MovePieceStep in Hn as LS.
  assert (L1 : T1.CorrectWithoutGameover (s1 s')). {
    assert (L1_1 : T1.MovePiece dyx (s1 s) = Some (s1 s'))
      by now destruct LS; congruence.
    assert (L1_2 : T1.CorrectWithoutGameover (s1 s)) by now keep_only Hc; firstorder.
    eapp T1P.MovePieceCorrectWithoutGameover.
  }
  assert (L2 : LevelCorrect s'). {
    assert (L2_1 : level s' = level s ∧ totalClearedLines s' = totalClearedLines s)
      by now keep_only LS; lia.
    assert (L2_2 : level s = 1 + totalClearedLines s / 10)
      by now destruct Hc; assumption.
    unfold LevelCorrect.
    destruct L2_1 as [Hl Ht].
    rewrite Hl, Ht.
    exact L2_2.
  }
  split; auto using L1, L2.
Qed.

Lemma RotatePieceCorrectWithoutGameover : ∀ [cw s s']
  (Hc : CorrectWithoutGameover s)
  (Hn : RotatePiece cw s = Some s'),
  CorrectWithoutGameover s'.
Proof.
  intros.
  apply RotatePieceStep in Hn as LS.
  assert (L1 : T1.CorrectWithoutGameover (s1 s')). {
    assert (L1_1 : T1.RotatePiece cw (s1 s) = Some (s1 s'))
      by now destruct LS; congruence.
    assert (L1_2 : T1.CorrectWithoutGameover (s1 s)) by now keep_only Hc; firstorder.
    eapp T1P.RotatePieceCorrectWithoutGameover.
  }
  assert (L2 : LevelCorrect s'). {
    assert (L2_1 : level s' = level s ∧ totalClearedLines s' = totalClearedLines s)
      by now keep_only LS; lia.
    assert (L2_2 : level s = 1 + totalClearedLines s / 10)
      by now destruct Hc; assumption.
    unfold LevelCorrect.
    destruct L2_1 as [Hl Ht].
    rewrite Hl, Ht.
    exact L2_2.
  }
  split; auto using L1, L2.
Qed.

Lemma FixPieceCorrectWithoutGameover : ∀ [p_new s s']
  (Hc : CorrectWithoutGameover s)
  (Hn : FixPiece p_new s = Some s'),
  CorrectWithoutGameover s'.
Proof.
  intros.
  apply FixPieceStep in Hn as LS.
  assert (L1 : T1.CorrectWithoutGameover (s1 s')). {
    assert (L1_1 : T1.FixPiece p_new (s1 s) = Some (s1 s'))
      by now destruct LS; congruence.
    assert (L1_2 : T1.CorrectWithoutGameover (s1 s)) by now keep_only Hc; firstorder.
    eapp T1P.FixPieceCorrectWithoutGameover.
  }
  assert (L2 : LevelCorrect s'). {
    set (clearedLines := clearedLines (s1 s')).
    set (totalClearedLines' := (totalClearedLines s + clearedLines)%nat).
    assert (L2_1 : level s' = 1 + totalClearedLines' / 10)
      by now keep_only LS; simpl in LS; tauto.
    assert (L2_2 : totalClearedLines s' = totalClearedLines')
      by now keep_only LS; simpl in LS; tauto.
    rewrite <- L2_2 in L2_1.
    exact L2_1.
  }
  split; auto using L1, L2.
Qed.

(* Used by T3's HoldPiece; needs the weak gameover fact about s1 s to thread
into T1P.NewPieceStateCorrectWithoutGameover. *)
Lemma NewPieceStateCorrectWithoutGameover : ∀ (p_new : Piece) (s : State)
  (Hc : CorrectWithoutGameover s)
  (Hg : ForbiddenGrid ∩ T1.mg (s1 s) ⊈ ∅ = true → T1.gameover (s1 s) = true),
  CorrectWithoutGameover (UnchangedT2Part s (T1.NewPieceState p_new (s1 s))).
Proof.
  intros.
  set (s' := UnchangedT2Part s (T1.NewPieceState p_new (s1 s))).
  assert (L1 : T1.CorrectWithoutGameover (s1 s')). {
    assert (L1_1 : T1.CorrectWithoutGameover (s1 s)) by now destruct Hc.
    eapp T1P.NewPieceStateCorrectWithoutGameover.
  }
  assert (L2 : LevelCorrect s'). {
    assert (L2_1 : level s' = level s) by reflexivity.
    assert (L2_2 : totalClearedLines s' = totalClearedLines s) by reflexivity.
    unfold LevelCorrect; rewrite L2_1, L2_2; now destruct Hc.
  }
  split; auto using L1, L2.
Qed.

Lemma NextCorrect : ∀ [e s s']
  (Hc : Correct s)
  (He : Next e s = Some s'),
  Correct s'.
Proof.
  intros.
  assert (L1 : ∀ [dyx] (Hn : MovePiece dyx s = Some s'), Correct s'). {
    intros.
    apply MovePieceStep in Hn as LS.
    assert (L1_1 : T1.Correct (s1 s')). {
      (* 1. MovePiece succeeded, so T1.MovePiece succeeded and produced (s1 s') unchanged. *)
      assert (L1_1_1 : T1.MovePiece dyx (s1 s) = Some (s1 s'))
        by now destruct LS; congruence.
      (* 2. s is correct, i.e. its T1 part is T1.Correct (by definition of Correct). *)
      assert (L1_1_2 : T1.Correct (s1 s)) by now keep_only Hc; firstorder.
      (* 3. T1.MovePieceCorrect transfers correctness across the T1 move. *)
      eapp T1P.MovePieceCorrect.
    }
    assert (L1_2 : LevelCorrect s'). {
      assert (L1_2_1 : level s' = level s ∧ totalClearedLines s' = totalClearedLines s)
        by now keep_only LS; lia.
      assert (L1_2_2 : level s = 1 + totalClearedLines s / 10)
        by now destruct Hc; assumption.
      unfold LevelCorrect.
      destruct L1_2_1 as [Hl Ht].
      rewrite Hl, Ht.
      exact L1_2_2.
    }
    split; auto using L1_1, L1_2.
  }
  assert (L2 : ∀ [cw] (Hn : RotatePiece cw s = Some s'), Correct s'). {
    intros.
    apply RotatePieceStep in Hn as LS.
    assert (L2_1 : T1.Correct (s1 s')). {
      assert (L2_1_1 : T1.RotatePiece cw (s1 s) = Some (s1 s'))
        by now destruct LS; congruence.
      assert (L2_1_2 : T1.Correct (s1 s)) by now keep_only Hc; firstorder.
      eapp T1P.RotatePieceCorrect.
    }
    assert (L2_2 : LevelCorrect s'). {
      assert (L2_2_1 : level s' = level s ∧ totalClearedLines s' = totalClearedLines s)
        by now keep_only LS; lia.
      assert (L2_2_2 : level s = 1 + totalClearedLines s / 10)
        by now destruct Hc; assumption.
      unfold LevelCorrect.
      destruct L2_2_1 as [Hl Ht].
      rewrite Hl, Ht.
      exact L2_2_2.
    }
    split; auto using L2_1, L2_2.
  }
  assert (L3 : ∀ [p_new] (Hn : FixPiece p_new s = Some s'), Correct s'). {
    intros.
    apply FixPieceStep in Hn as LS.
    assert (L3_1 : T1.Correct (s1 s')). {
      assert (L3_1_1 : T1.FixPiece p_new (s1 s) = Some (s1 s'))
        by now destruct LS; congruence.
      assert (L3_1_2 : T1.Correct (s1 s)) by now keep_only Hc; firstorder.
      eapp T1P.FixPieceCorrect.
    }
    assert (L3_2 : LevelCorrect s'). {
      set (clearedLines := clearedLines (s1 s')).
      set (totalClearedLines' := (totalClearedLines s + clearedLines)%nat).
      assert (L3_2_1 : level s' = 1 + totalClearedLines' / 10)
        by now keep_only LS; simpl in LS; tauto.
      assert (L3_2_2 : totalClearedLines s' = totalClearedLines')
        by now keep_only LS; simpl in LS; tauto.
      rewrite <- L3_2_2 in L3_2_1.
      exact L3_2_1.
    }
    split; auto using L3_1, L3_2.
  }
  assert (L4 : ∀ [p_new] (Hn : FallStep p_new s = Some s'), Correct s'). {
    intros.
    unfold FallStep in Hn.
    destruct MovePiece eqn: Hm in Hn.
    - assert (L4_1 : MovePiece (-1, 0)%Z s = Some s') by now rewrite <- Hm in Hn.
      now apply L1 in L4_1.
    - Check (Hn : FixPiece p_new s = Some s').
      now apply L3 in Hn.
  }
  assert (L5 : ∀ (Hn : Next Stutter s = Some s'), Correct s'). {
    intros.
    assert (L5_1 : s' = s) by now injection Hn.
    now rewrite <- L5_1 in Hc.
  }
  destruct e in He; eauto using L1, L2, L3, L4, L5.
Qed.

Theorem SpecCorrect : ∀ e s s',
    (∀ p, Correct (Init p))
  ∧ (Correct s → Next e s = Some s' → Correct s').
Proof. split; eauto using InitCorrect, NextCorrect. Qed.


(* ========================================================================= *)
(* Step invariants                                                           *)
(* ========================================================================= *)

Theorem StepNonDecreasingScore : ∀ s s',
  NonDecreasingScore s s'.
Proof.
  unfold NonDecreasingScore.
  intros.
  assert (L1 : ∀ dyx (Hm : MovePiece dyx s = Some s'), score s <= score s')
    by now intros; apply MovePieceStep in Hm; lia.
  assert (L2 : ∀ cw (Hm : RotatePiece cw s = Some s'), score s <= score s')
    by now intros; apply RotatePieceStep in Hm; lia.
  assert (L3 : ∀ p_new (Hm : FixPiece p_new s = Some s'), score s <= score s'). {
    intros.
    set (clearedLines' := clearedLines (s1 s')).
    set (combo' := (if clearedLines' =? 0 then 0 else (combo s) + 1)).
    set (perfectClear' := EmptyGridb (mg s')).
    assert (L3_2_1 : score s' = (score s) + (Points clearedLines' (level s) (combo'-1) perfectClear'))
      by now apply FixPieceStep in Hm.
    enough (score s <= score s + Points clearedLines' (level s) (combo' - 1) perfectClear')
      by now rewrite L3_2_1.
    lia.
  }
  assert (L4 : ∀ p_new (Hm : FallStep p_new s = Some s'), score s <= score s'). {
    intros.
    unfold FallStep in Hm.
    destruct MovePiece eqn: Hf in Hm.
    - assert (L4_1 : MovePiece (-1, 0)%Z s = Some s') by now rewrite Hm in Hf.
      now apply L1 in L4_1.
    - Check (Hm : FixPiece p_new s = Some s').
      now apply L3 in Hm.
  }
  assert (L5 : ∀ (Hm : Next Stutter s = Some s'), score s <= score s'). {
    intros.
    enough (score s <= score s)
      by now apply StutterStep in Hm; rewrite Hm.
    lia.
  }
  destruct e in Hn; eauto using L1, L2, L3, L4, L5.
Qed.

Theorem StepNonDecreasingTotalClearedLines : ∀ [s s' e]
  (Hn : Next e s = Some s'),
  totalClearedLines s <= totalClearedLines s'.
Proof.
  intros.
  set (G := totalClearedLines s <= totalClearedLines s').
  assert (L1 : ∀ dyx (Hm : MovePiece dyx s = Some s'), G)
    by now intros; unfold G; apply MovePieceStep in Hm; lia.
  assert (L2 : ∀ cw (Hm : RotatePiece cw s = Some s'), G)
    by now intros; unfold G; apply RotatePieceStep in Hm; lia.
  assert (L3 : ∀ p_new (Hm : FixPiece p_new s = Some s'), G). {
    intros.
    set (clearedLines := clearedLines (s1 s')).
    set (totalClearedLines' := totalClearedLines s + clearedLines).
    assert (L3_2_1 : totalClearedLines s' = totalClearedLines s + clearedLines)
      by now apply FixPieceStep in Hm as L3_2_1_1; simpl in L3_2_1_1; lia.
    unfold G.
    enough (totalClearedLines s <= totalClearedLines s + clearedLines)
      by now rewrite L3_2_1.
    lia.
  }
  assert (L4 : ∀ p_new (Hm : FallStep p_new s = Some s'), G). {
    intros.
    unfold FallStep in Hm.
    destruct MovePiece eqn: Hf in Hm.
    - assert (L4_1 : MovePiece (-1, 0)%Z s = Some s') by now rewrite Hm in Hf.
      now apply L1 in L4_1.
    - Check (Hm : FixPiece p_new s = Some s').
      now apply L3 in Hm.
  }
  assert (L5 : ∀ (Hm : Next Stutter s = Some s'), G). {
    intros.
    assert (L5_1 : s' = s) by now apply StutterStep in Hm.
    unfold G; rewrite L5_1; lia.
  }
  destruct e in Hn; eauto using L1, L2, L3, L4, L5.
Qed.

Theorem StepNonDecreasingLevel : ∀ [s] s'
  (Hc : Correct s),
  NonDecreasingLevel s s'.
Proof.
  unfold NonDecreasingLevel.
  intros.
  enough (1 + totalClearedLines s / 10 <= 1 + totalClearedLines s' / 10). {
    assert (L1 : Correct s') by now apply NextCorrect in Hn.
    assert (L2 : level s = 1 + (totalClearedLines s) / 10)
      by now destruct Hc as [_ L2_1]; unfold LevelCorrect in L2_1.
    assert (L3 : level s' = 1 + (totalClearedLines s') / 10)
      by now destruct L1 as [_ L3_1]; unfold LevelCorrect in L3_1.
    now rewrite L2, L3.
  }
  enough (totalClearedLines s / 10 <= totalClearedLines s' / 10)
    by lia.
  enough (totalClearedLines s <= totalClearedLines s')
    by now apply Nat.Div0.div_le_mono; lia.
  now apply StepNonDecreasingTotalClearedLines in Hn. 
Qed.

Theorem StepScoreRisesOnClear (s s' : State) :
  ScoreRisesOnClear s s'.
Proof.
  unfold ScoreRisesOnClear.
  intros.
  enough (score s < score s') by trivial.
  set (clearedLines' := clearedLines (s1 s')).
  set (combo' := (if clearedLines' =? 0 then 0 else (combo s) + 1)).
  set (perfectClear' := EmptyGridb (mg s')).
  assert (L1 : score s' = score s + (Points clearedLines' (level s) (combo'-1) perfectClear'))
    by now apply FixPieceStep in Hn.
  rewrite L1.
  enough (0 < Points (clearedLines (s1 s')) (level s) (combo' - 1) perfectClear')
    by now unfold clearedLines'; lia.
  assert (L2 : ∀ clearedLines level combo perfectClear
              (Hv : 0 < level)
              (Hi : 0 < clearedLines),
              0 < Points clearedLines level combo perfectClear). {
    intros.
    assert (L2_1 : ∀ clearedLines level
                   (Hp : 0 < clearedLines)
                   (He : 0 < level),
                   0 < LineClearPoints clearedLines level). {
      intros.
      unfold LineClearPoints.
      keep_only Hp He.
      destruct clearedLines0 as [| [| [| [| n]]]]; simpl; nia.
    }
    unfold Points.
    pose proof (L2_1 clearedLines level Hi Hv) as H1.
    keep_only H1; lia.
  }
  assert (L3 : 0 < level s). {
    unfold Correct, LevelCorrect in Hc.
    assert (L3_1 : level s = 1 + totalClearedLines s / 10)
      by now destruct Hc.
    keep_only L3_1; lia.
  }
  apply (L2 (clearedLines (s1 s')) (level s) (combo' - 1) perfectClear' L3).
  exact Hl.
Qed.

(* NonDecreasingLevel is the only conjunct needing `Correct s`: FixPiece resets
 * level to `1 + totalClearedLines'/10`, which is below an arbitrary `level s`
 * unless LevelCorrect holds. *)
Theorem CorrectStepHold : ∀ [s] s'
  (Hc : Correct s),
  CorrectStep s s'.
Proof.
  intros; unfold CorrectStep; repeat split; auto using StepNonDecreasingScore,
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

#[local] Ltac apply_cong Def H :=
  intros;
  apply Def in H as [H1 _];
  keep_only H1;
  congruence.

Lemma RefineNext : ∀ [s2 s2' e2]
  (Hn : T2.Next e2 s2 = Some s2'),
  T1.Next (fₑ e2) (fₛ s2) = Some (fₛ s2').
Proof.
  intros.
  unfold fₛ. (* fₛ = s1 *)
  assert (L1 : ∀ [dyx]
               (Hm : MovePiece dyx s2 = Some s2'),
               T1.MovePiece dyx (s1 s2) = Some (s1 s2'))
    by now apply_cong MovePieceStep Hm.
  assert (L2 : ∀ cw (Hm : RotatePiece cw s2 = Some s2'),
               T1.RotatePiece cw (s1 s2) = Some (s1 s2'))
    by now apply_cong RotatePieceStep Hm.
  assert (L3 : ∀ p_new (Hm : FixPiece p_new s2 = Some s2'),
               T1.FixPiece p_new (s1 s2) = Some (s1 s2'))
    by now apply_cong FixPieceStep Hm.
  assert (L4 : ∀ p_new (Hm : FallStep p_new s2 = Some s2'),
               T1.FallStep p_new (s1 s2) = Some (s1 s2')). {
    keep_only L1 L3 Hn.
    intros.
    unfold FallStep in Hm.
    destruct MovePiece eqn: H1 in Hm.
    - (* MovePiece succeeds *)
      unfold T1.FallStep.
      rewrite Hm in H1.
      apply L1 in H1.
      now rewrite H1.
    - (* FixPiece succeeds *)
      assert (L4_1 : T1.MovePiece (-1, 0)%Z (s1 s2) = None) 
        by now apply MovePieceFail in H1.
      unfold T1.FallStep.
      enough (T1.FixPiece p_new (s1 s2) = Some (s1 s2')) by now rewrite L4_1.
      now rewrite (L3 p_new Hm).
  }
  assert (L5 : ∀ (Hm : Next Stutter s2 = Some s2'),
               T1.Next (fₑ Stutter) (s1 s2) = Some (s1 s2')). {
    intros.
    apply StutterStep in Hm as L5_1.
    simpl; congruence.
  }
  destruct e2; (eapp L1 || eapp L2 || eapp L3 || eapp L4 || eapp L5).
Qed.

Theorem SpecRefine : T2RefinesT1.
Proof. split; auto using RefineInit, RefineNext. Qed.


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
  destruct (T2.Next (gₑ e1) s2) eqn: Hn.
  - Check (Hn : Next (gₑ e1) s2 = Some s).
    assert (L1 : fₛ s = s1'). {
      assert (L1_1 : T1.Next (fₑ (gₑ e1)) (fₛ s2) = Some (fₛ s))
        by now apply RefineNext in Hn.
      assert (L1_2 : T1.Next e1 s1 = Some (fₛ s))
        by now rewrite feRetractsGe, H1 in L1_1.
      now rewrite H2 in L1_2; inject L1_2.
    }
    enough (Some s = Some s ∧ fₛ s = s1') by now exists s.
    split; (reflexivity || exact L1).
  - Check (Hn : Next (gₑ e1) s2 = None).
    unfold T1.Next in H2.
    unfold Next, MovePiece, RotatePiece, FixPiece in Hn.
    unfold fₛ in H1.
    rewrite <- H1 in H2.
    assert (L1 : ∀ pNew
        (Hf1 : T1.FallStep pNew (T2.s1 s2) = Some s1')
        (Hf2 : FallStep pNew s2 = None),
        ∃ s2' : State, None = Some s2' ∧ fₛ s2' = s1'). {
      intros.
      keep_only Hf1 Hf2.
      unfold T1.FallStep in Hf1.
      unfold FallStep, MovePiece in Hf2.
      destruct (T1.MovePiece ((-1)%Z, 0%Z) (T2.s1 s2)).
      -- unfold FallStep in Hf2. discriminate Hf2.
      -- simpl in Hf2.
         unfold FixPiece in Hf2.
         rewrite Hf1 in Hf2.
         discriminate Hf2.
    }
    destruct e1; simpl in Hn;
      (try rewrite H2 in Hn; discriminate Hn) || eapp L1.
Qed.

Theorem T2AllowsAllT1Hold : T2AllowsAllT1.
Proof.
  (* generalize the starting states so the IH applies at every point along the run *)
  assert (L1 : ∀ es1 s1 s2 s1'
      (Hfs : fₛ s2 = s1)
      (Hrun : RunT1 es1 s1 = Some s1'),
      ∃ s2', RunT2 (map gₑ es1) s2 = Some s2' /\ fₛ s2' = s1'). {
    intros es1.
    induction es1 as [| e1 es1' IH]. intros.
    - (* es1 = [] : RunT1 returns s1 itself *)
      exists s2. simpl in Hrun. split; (reflexivity || congruence).
    - (* es1 = e1 :: es1' *)
      intros.
      simpl in Hrun.
      destruct (T1.Next e1 s1) as [s1'' | ] eqn:Hstep; [ | discriminate].
      (* apply the single-step lemma to lift this step to T2 *)
      destruct (StepLifts Hfs Hstep) as [s2'' [Hstep2 Hfs2]].
      simpl. rewrite Hstep2.
      (* recurse on the rest of the trace, from (s1'', s2'') *)
      eapp IH.
  }
  unfold T2AllowsAllT1. intros p es1 s1'.
  enough (fₛ (T2.Init p) = T1.Init p)
    by now apply (L1 es1 (T1.Init p) (T2.Init p) s1').
  assert (L2 : ∀ p, fₛ (T2.Init p) = T1.Init p)
    by now pose proof SpecRefine; tauto.
  exact (L2 p).
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
  intros p_new s Hc.
  set (s' := UnchangedT2Part s (T1.NewPieceState p_new (s1 s))).
  assert (L1 : T1.Correct (s1 s')). {
    assert (L1_1 : T1.Correct (s1 s)) by now destruct Hc.
    keep_only L1_1; now apply T1P.NewPieceStateCorrect.
  }
  assert (L2 : LevelCorrect s'). {
    (* level and totalClearedLines are copied verbatim by UnchangedT2Part *)
    assert (L2_1 : level s' = level s) by reflexivity.
    assert (L2_2 : totalClearedLines s' = totalClearedLines s) by reflexivity.
    unfold LevelCorrect; rewrite L2_1, L2_2; now destruct Hc.
  }
  split; auto using L1, L2.
Qed.
