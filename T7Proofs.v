From Tetris Require Import T7 Notations.
From Tetris Require T1 T6.
From Tetris Require T1Proofs T5Proofs T6Proofs.
Module T1P := T1Proofs.
Module T5P := T5Proofs.
Module T6P := T6Proofs.
Import (notations) T1.
Import T1(AxiomsInitialMainGrid, Grid, L, HW, H, W, YX, Y, X, InitialMainGrid,
  ForbiddenGrid, Full, GridIntersect, GridUnion, GridTranslate, Constant).
From Stdlib Require Import Lia PeanoNat ZArith Bool List.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Hammer Require Import Tactics.
Import ListNotations.

#[local] Infix "=?" := PlayerEqb (at level 70) : player_scope.
#[local] Open Scope nat_scope.


(* ========================================================================= *)
(* Helpers                                                                   *)
(* ========================================================================= *)

Lemma PlayerEqbEq1 : ∀ [pl1 pl2]
  (H1 : PlayerEqb pl1 pl2 = true),
  pl1 = pl2.
Proof. intros; destruct (PlayerEqbEq pl1 pl2); auto. Qed.

Lemma PlayerEqbEq2 : ∀ [pl1 pl2]
  (H1 : pl1 = pl2),
  PlayerEqb pl1 pl2 = true.
Proof. intros; destruct (PlayerEqbEq pl1 pl2); auto. Qed.

Lemma PlayerEqbEq3 : ∀ [pl1 pl2]
  (H1 : PlayerEqb pl1 pl2 = false),
  pl1 ≠ pl2.
Proof.
  intros pl1 pl2 H1 L1.
  Check (L1 : pl1 = pl2).
  enough (False) by trivial.
  apply PlayerEqbEq2 in L1.
  rewrite H1 in L1.
  discriminate.
Qed.

Lemma PlayerEqbEq4 : ∀ [pl1 pl2]
  (H1 : pl1 ≠ pl2),
  PlayerEqb pl1 pl2 = false.
Proof.
  intros pl1 pl2 H1.
  destruct (PlayerEqb pl1 pl2) eqn: L1.
  - apply PlayerEqbEq1 in L1.
    contradiction.
  - reflexivity.
Qed.

Lemma PlayerEqbReflexive : ∀ pl,
  PlayerEqb pl pl = true.
Proof.  sauto use: PlayerEqbEq2.  Qed.

Lemma InitSelfViewAccurate : ∀ bags H,
  SelfViewAccurate (Init bags H).
Proof. sauto use: PlayerEqbReflexive unfold: SelfViewAccurate, gameover. Qed.

Lemma IfSome : ∀ [A : Type] [a] [cond : bool] [optA : option A]
  (H1 : (if cond then optA else None) = Some a),
  optA = Some a.
Proof.
  intros; destruct cond in H1; (exact H1 || discriminate H1).
Qed.

Lemma UpdatePlayerSetsOwnGameoverView : ∀ [s s' pl s6']
  (H1 : UpdatePlayer s pl s6' = s'),
  gameoverView s' pl pl = gameover s' pl.
Proof.
  intros.
  enough ((if PlayerEqb pl pl && PlayerEqb pl pl
      then T6.gameover s6'
      else gameoverView s pl pl) =
      T6.gameover (if PlayerEqb pl pl then s6' else s6 s pl)). {
    rewrite <- H1; unfold gameover, gameoverView, UpdatePlayer.
    now simpl.
  }
  now rewrite (PlayerEqbReflexive pl).
Qed.

Section Player.
Open Scope player_scope.

Lemma PointUpdateSelfViewAccurate : ∀ [s s' pl s6new]
  (H1 : SelfViewAccurate s)
  (H2 : s6 s' = λ pl2, if pl2 =? pl then s6new else s6 s pl2)
  (H3 : gameoverView s' = λ obs obsd,
      if (obs =? pl) && (obsd =? pl) then T6.gameover s6new else gameoverView s obs obsd),
  SelfViewAccurate s'.
Proof. unfold SelfViewAccurate, gameover in *; sauto. Qed.

Lemma UpdatePlayerPreservesViewAccurate : ∀ [s s' pl s6']
  (H1 : SelfViewAccurate s)
  (H2 : UpdatePlayer s pl s6' = s'),
  SelfViewAccurate s'.
Proof.
  intros.
  assert (L1 : s6 s' = λ pl2, if pl2 =? pl then s6' else s6 s pl2) by now rewrite <- H2.
  apply (PointUpdateSelfViewAccurate H1 L1); now rewrite <- H2.
Qed.

End Player.

Lemma GuardedUpdateSelfViewAccurate : ∀ [A s s' pl] [f : A → option T6.State] [x : A]
  (H1 : SelfViewAccurate s)
  (H2 : (if ! WinnerMulti s pl then option_map (UpdatePlayer s pl) (f x) else None) = Some s'),
  SelfViewAccurate s'.
Proof. sauto use: UpdatePlayerPreservesViewAccurate, IfSome, T5P.OptionMapSome. Qed.


(* ========================================================================= *)
(* SelfViewAccurate                                                          *)
(* ========================================================================= *)

(* If MovePiece triggers for player pl, then T6.MovePiece also is, and
UpdatePlayer sets her gameover view to her real gameover status, keeping other
values untouched.
*)
Lemma MovePieceSelfViewAccurate : ∀ [s s' pl dyx]
  (H1 : SelfViewAccurate s)
  (H2 : MovePiece pl dyx s = Some s'),
  SelfViewAccurate s'.
Proof. intros; exact (GuardedUpdateSelfViewAccurate H1 H2). Qed.

(* Same reasoning as for MovePiece. *)
Lemma RotatePieceSelfViewAccurate : ∀ [s s' pl dyx]
  (H1 : SelfViewAccurate s)
  (H2 : RotatePiece pl dyx s = Some s'),
  SelfViewAccurate s'.
Proof. intros; exact (GuardedUpdateSelfViewAccurate H1 H2). Qed.

Lemma NewMainGridGameoverStateGameover : ∀ mg gmover s6,
  T6.gameover (NewMainGridGameoverState mg gmover s6) = gmover.
Proof.
  intros; now unfold T6.gameover, NewMainGridGameoverState.
Qed.

Section Player.
Open Scope player_scope.

Lemma FixPieceSelfViewAccurate : ∀ [s s' pl holes Hhole bagNew Hbag]
  (H1 : SelfViewAccurate s)
  (H2 : FixPiece pl holes Hhole bagNew Hbag s = Some s'),
  SelfViewAccurate s'.
Proof.
  intros.
  unfold FixPiece in H2.
  destruct (! WinnerMulti s pl) eqn: L1.
  - destruct (T6.FixPiece bagNew Hbag (s6 s pl)) as [s6' |] eqn: L2. (* Case ! WinnerMulti s pl = true *)
    + unfold option_map in H2.
      inject H2.  (* Case T6.FixPiece bagNew Hbag (s6 s pl) = Some s0 *)
      destruct ((PlayerCount =? 1)%nat) eqn: L3.
      * now apply UpdatePlayerPreservesViewAccurate in H2. (* Case single player *)
      * (* Case multiplayer *)
        assert (L3_1 : s6 s' = λ pl2, if pl2 =? pl then
            NewMainGridGameoverState (FP.CroppedMg' s pl s6' holes) (FP.Gameover' s pl s6' holes) s6'
            else s6 s pl2)
          by now rewrite <- H2.
        apply (PointUpdateSelfViewAccurate H1 L3_1); now rewrite <- H2.
    + discriminate H2. (* Case T6.FixPiece bagNew Hbag (s6 s pl) = None *)
  - discriminate H2. (* Case ! WinnerMulti s pl = false *)
Qed.

End Player.

(* Forward to MovePiece and FixPiece proofs. *)
Lemma FallStepSelfViewAccurate : ∀ [s s' pl holes Hhole bagNew Hbag]
  (H1 : SelfViewAccurate s)
  (H2 : FallStep pl holes Hhole bagNew Hbag s = Some s'),
  SelfViewAccurate s'.
Proof.
  intros.
  unfold FallStep in H2.
  destruct (! WinnerMulti s pl) in H2.
  - destruct (MovePiece pl (-1, 0)%Z s) eqn: L1.
    + Check (H2 : Some s0 = Some s').
      rewrite H2 in L1.
      apply (MovePieceSelfViewAccurate H1 L1).
    + apply (FixPieceSelfViewAccurate H1 H2).
  - discriminate H2.
Qed.

(* Same reasoning as for MovePiece. *)
Lemma HoldPieceSelfViewAccurate : ∀ [s s' pl holes Hhole bagNew Hbag]
  (H1 : SelfViewAccurate s)
  (H2 : HoldPiece pl holes Hhole bagNew Hbag s = Some s'),
  SelfViewAccurate s'.
Proof. intros; exact (GuardedUpdateSelfViewAccurate H1 H2). Qed.

Lemma NewPieceYXStatePreservesSelfViewAccurate : ∀ [s]
  (H1 : SelfViewAccurate s),
  ∀ pyxNew pl, SelfViewAccurate (NewPieceYXState pyxNew pl s).
Proof.
  intros .
  set (s' := NewPieceYXState pyxNew pl s).
  assert (L1 : gameover s' = gameover s). {
    unfold gameover.
    apply functional_extensionality.
    intro pl0.
    enough (T6.gameover (if (pl0 =? pl)%player then T6.NewPieceYXState pyxNew (s6 s pl)
                         else s6 s pl0) =
            T6.gameover (s6 s pl0))
      by now simpl.
    destruct (PlayerEqb pl0 pl) eqn: Le.
    -  (* Case PlayerEqb pl0 pl = true *)
      enough (T6.gameover (T6.NewPieceYXState pyxNew (s6 s pl)) = T6.gameover (s6 s pl0)) by trivial.
      assert (L1_1 : pl0 = pl) by now apply PlayerEqbEq1.
      now rewrite L1_1.
    - reflexivity. (* Case PlayerEqb pl0 pl = false *)
  }
  assert (L2 : ∀ pl0, gameoverView s' pl0 = gameoverView s pl0)
    by reflexivity.
  unfold SelfViewAccurate.
  intros.
  destruct (PlayerEqb pl0 pl) eqn: Le.
  - (* Case PlayerEqb pl0 pl = true *)
    enough (gameoverView s' pl pl = gameover s' pl) by now rewrite (PlayerEqbEq1 Le).
    rewrite L1, L2; exact (H1 pl).
  - (* Case PlayerEqb pl0 pl = false *)
    apply PlayerEqbEq3 in Le.
    rewrite (L2 pl0), L1; exact (H1 pl0).
Qed.

(* Forward to FixPiece. *)
Lemma DropPieceSelfViewAccurate : ∀ [s s' pl holes Hhole bagNew Hbag]
  (H1 : SelfViewAccurate s)
  (H2 : DropPiece pl holes Hhole bagNew Hbag s = Some s'),
  SelfViewAccurate s'.
Proof.
  intros.
  unfold DropPiece in H2.
  assert (L1 : SelfViewAccurate (NewPieceYXState (gy s pl, px s pl) pl s)) by
    apply (NewPieceYXStatePreservesSelfViewAccurate H1).
  apply (FixPieceSelfViewAccurate L1 H2).
Qed.

(* Same reasoning as for MovePiece. *)
Lemma RotateKickPieceSelfViewAccurate : ∀ [s s' pl cw]
  (H1 : SelfViewAccurate s)
  (H2 : RotateKickPiece pl cw s = Some s'),
  SelfViewAccurate s'.
Proof. intros; exact (GuardedUpdateSelfViewAccurate H1 H2). Qed.

Lemma ReceiveGameoverMessageSelfViewAccurate : ∀ [s s' pl from ms]
    (H1 : SelfViewAccurate s)
    (H2 : NoSelfMessage s)
    (H3 : messages s from pl = GameoverMessage :: ms)
    (Hs : s6 s' = s6 s)
    (Hg : gameoverView s' = λ obs obsd,
      if PlayerEqb obs pl && PlayerEqb obsd from then true else gameoverView s obs obsd),
    SelfViewAccurate s'.
  (* Others views are unchanged and the view pl has of herself cannot change per
     NoSelfMessage. *)
  intros.
  assert (L1 : gameover s' = gameover s) by now unfold gameover; rewrite Hs.
  assert (L2 : ∀ pl0 (Hn : pl0 ≠ pl), gameoverView s' pl0 pl0 = gameover s' pl0). {
    intros.
    assert (L2_1 : PlayerEqb pl0 pl = false) by now apply PlayerEqbEq4 in Hn.
    enough (gameoverView s pl0 pl0 = gameover s pl0) by now rewrite Hg, L1, L2_1.
    exact (H1 pl0).
  }
  assert (L3 : gameoverView s' pl pl = gameover s' pl). {
    rewrite Hg, L1.
    rewrite (PlayerEqbReflexive pl); simpl.
    destruct (PlayerEqb pl from) eqn: L3_1.
    - unfold NoSelfMessage in H2. (* PlayerEqb pl from = true *)
      assert (L3_2 : messages s pl pl = []) by now exact (H2 pl).
      assert (L3_3 : pl = from) by now apply PlayerEqbEq1 in L3_1.
      assert (L3_4 : messages s pl pl = GameoverMessage :: ms) by now rewrite <- L3_3 in H3.
      assert (L3_5 : GameoverMessage :: ms = []) by now rewrite L3_4 in L3_2.
      discriminate L3_5.
    - exact (H1 pl). (* PlayerEqb pl from = false *)
  }
  unfold SelfViewAccurate.
  intros pl0.
  destruct (PlayerEqb pl0 pl) eqn: L4_1.
  - apply PlayerEqbEq1 in L4_1. (* PlayerEqb pl0 pl = true *)
    rewrite L4_1.
    exact L3.
  - apply PlayerEqbEq3 in L4_1. (* PlayerEqb pl0 pl = false *)
    exact (L2 pl0 L4_1).
Qed.

Lemma UnchangedSelfViewAccurate : ∀ [s s']
  (H1 : SelfViewAccurate s)
  (H2 : s6 s' = s6 s)
  (H3 : gameoverView s' = gameoverView s),
  SelfViewAccurate s'.
Proof. unfold SelfViewAccurate, gameover in *; sauto. Qed.

Lemma ReceiveMessageSelfViewAccurate : ∀ [s s' pl from]
  (H1 : SelfViewAccurate s)
  (H2 : NoSelfMessage s)
  (H3 : ReceiveMessage pl from s = Some s'),
  SelfViewAccurate s'.
Proof.
  intros.
  unfold ReceiveMessage in H3.
  destruct (connected s pl) eqn: L1 in H3.
  - (* Case connected s pl = true *)
    destruct (messages s from pl) as [|m ms] eqn: L2.
    + discriminate H3. (* Case messages s from pl = [] *)
    + destruct m as [n| |] eqn: L3. (* Case messages s from pl = m :: ms *)
      * inject H3. (* m = GarbageMessage n *)
        assert (L3_1 : s6 s' = s6 s) by now rewrite <- H3.
        assert (L3_2 : gameoverView s' = gameoverView s) by now rewrite <- H3.
        apply (UnchangedSelfViewAccurate H1 L3_1 L3_2).
      * (* Case m = GameoverMessage *)
        inject H3. (* Case m = GarbageMessage n *)
        assert (L3_1 : s6 s' = s6 s) by now rewrite <- H3.
        assert (L3_2 : gameoverView s' = λ obs obsd,
            if PlayerEqb obs pl && PlayerEqb obsd from then true else gameoverView s obs obsd)
          by now rewrite <- H3.
        apply (ReceiveGameoverMessageSelfViewAccurate H1 H2 L2 L3_1 L3_2).
      * (* Case m = DisconnectMessage *)
        inject H3.
        assert (L3_1 : s6 s' = s6 s) by now rewrite <- H3.
        assert (L3_2 : gameoverView s' = gameoverView s) by now rewrite <- H3.
        apply (UnchangedSelfViewAccurate H1 L3_1 L3_2).
    - (* Case connected s pl = false *)
      discriminate H3.
Qed.

Lemma DisconnectPlayerSelfViewAccurate : ∀ [s s' pl]
  (H1 : SelfViewAccurate s)
  (H2 : DisconnectPlayer pl s = Some s'),
  SelfViewAccurate s'.
Proof. intros; unfold DisconnectPlayer in H2; sauto use: UnchangedSelfViewAccurate. Qed.

(* Same reasoning as DisconnectSelfViewAccurate. *)
Lemma NoticeDisconnectionSelfViewAccurate : ∀ [s s' pl]
  (H1 : SelfViewAccurate s)
  (H2 : NoticeDisconnection pl s = Some s'),
  SelfViewAccurate s'.
Proof. intros; unfold NoticeDisconnection in H2; sauto use: UnchangedSelfViewAccurate. Qed.

Lemma StutterSelfViewAccurate : ∀ [s s']
  (H1 : SelfViewAccurate s)
  (H2 : Some s = Some s'),
  SelfViewAccurate s'.
Proof. intros; inject H2; now rewrite <- H2. Qed.

Lemma NextSelfViewAccurate : ∀ [pl e s s']
  (H1 : NoSelfMessage s)
  (H2 : SelfViewAccurate s)
  (H3 : Next pl e s = Some s'),
  SelfViewAccurate s'.
Proof.
  intros.
  destruct e in H3; simpl in H3; (
    eapp MovePieceSelfViewAccurate || eapp RotatePieceSelfViewAccurate ||
    eapp FixPieceSelfViewAccurate || eapp FallStepSelfViewAccurate ||
    eapp HoldPieceSelfViewAccurate || eapp DropPieceSelfViewAccurate ||
    eapp RotateKickPieceSelfViewAccurate || eapp ReceiveMessageSelfViewAccurate ||
    eapp DisconnectPlayerSelfViewAccurate || eapp NoticeDisconnectionSelfViewAccurate ||
    eapp StutterSelfViewAccurate).
Qed.

Theorem SpecSelfViewAccurate :
   (∀ bags H, SelfViewAccurate (Init bags H))
 ∧ (∀ [pl e s s']
      (H1 : NoSelfMessage s)
      (H2 : SelfViewAccurate s)
      (H3 : Next pl e s = Some s'),
      SelfViewAccurate s').
Proof.
  split; (eapp InitSelfViewAccurate || eapp NextSelfViewAccurate).
Qed.


(* ========================================================================= *)
(* GameoverMonotone                                                          *)
(* ========================================================================= *)

Lemma MovePieceGameoverMonotone : ∀ [s s' pl1 pl2 dyx]
  (H1 : MovePiece pl1 dyx s = Some s')
  (H2 : gameover s pl2 = true),
  gameover s' pl2 = true.
Proof.
  intros.
  apply IfSome, T5P.OptionMapSome in H1.
  destruct H1 as [s6' [E1 E2]].
  unfold gameover in *; rewrite <- E2; simpl.
  destruct (PlayerEqb pl2 pl1) eqn: L1.
  - apply PlayerEqbEq1 in L1.
    unfold T6.gameover; rewrite (T5P.MovePieceUnchangedGameover E1), <- L1.
    exact H2.
  - exact H2.
Qed.

Lemma RotatePieceGameoverMonotone : ∀ [s s' pl1 pl2 dyx]
  (H1 : RotatePiece pl1 dyx s = Some s')
  (H2 : gameover s pl2 = true),
  gameover s' pl2 = true.
Proof.
  intros.
  apply IfSome, T5P.OptionMapSome in H1.
  destruct H1 as [s6' [E1 E2]].
  unfold gameover in *; rewrite <- E2; simpl.
  destruct (PlayerEqb pl2 pl1) eqn: L1.
  - apply PlayerEqbEq1 in L1.
    unfold T6.gameover; rewrite (T5P.RotatePieceUnchangedGameover E1), <- L1.
    exact H2.
  - exact H2.
Qed.

Lemma HoldPieceGameoverMonotone : ∀ [s s' pl1 pl2 holes Hhole bagNew Hbag]
  (H1 : HoldPiece pl1 holes Hhole bagNew Hbag s = Some s')
  (H2 : gameover s pl2 = true),
  gameover s' pl2 = true.
Proof.
  intros.
  apply IfSome, T5P.OptionMapSome in H1.
  destruct H1 as [s6' [E1 E2]].
  unfold gameover in *; rewrite <- E2; simpl.
  destruct (PlayerEqb pl2 pl1) eqn: L1.
  - apply PlayerEqbEq1 in L1; rewrite L1 in H2.
    unfold T6.gameover in H2; rewrite (T5P.HoldPieceNotGameover E1) in H2.
    discriminate H2.
  - exact H2.
Qed.

Lemma RotateKickPieceGameoverMonotone : ∀ [s s' pl1 pl2 cw]
  (H1 : RotateKickPiece pl1 cw s = Some s')
  (H2 : gameover s pl2 = true),
  gameover s' pl2 = true.
Proof.
  intros.
  apply IfSome, T5P.OptionMapSome in H1.
  destruct H1 as [s6' [E1 E2]].
  unfold gameover in *; rewrite <- E2; simpl.
  destruct (PlayerEqb pl2 pl1) eqn: L1.
  - apply PlayerEqbEq1 in L1; rewrite L1 in H2.
    rewrite (T6P.RotateKickNotGameover E1) in H2.
    discriminate H2.
  - exact H2.
Qed.

Lemma FixPieceGameoverMonotone : ∀ [s s' pl1 pl2 holes Hhole bagNew Hbag]
  (H1 : FixPiece pl1 holes Hhole bagNew Hbag s = Some s')
  (H2 : gameover s pl2 = true),
  gameover s' pl2 = true.
Proof.
  intros.
  unfold FixPiece in H1.
  destruct (! WinnerMulti s pl1) eqn: L1; [ | discriminate H1].
  destruct (T6.FixPiece bagNew Hbag (s6 s pl1)) as [s6' |] eqn: L2; [ | discriminate H1].
  unfold option_map in H1; inject H1.
  destruct (PlayerEqb pl2 pl1) eqn: L3.
  - apply PlayerEqbEq1 in L3; rewrite L3 in H2.
    unfold gameover, T6.gameover in H2. rewrite (T5P.FixPieceNotGameover L2) in H2.
    discriminate H2.
  - assert (L4 : s6 s' pl2 = s6 s pl2). {
      rewrite <- H1.
      destruct ((PlayerCount =? 1)%nat); simpl; now rewrite L3.
    }
    unfold gameover; rewrite L4; exact H2.
Qed.

Lemma FallStepGameoverMonotone : ∀ [s s' pl1 pl2 holes Hhole bagNew Hbag]
  (H1 : FallStep pl1 holes Hhole bagNew Hbag s = Some s')
  (H2 : gameover s pl2 = true),
  gameover s' pl2 = true.
Proof.
  intros.
  unfold FallStep in H1.
  destruct (! WinnerMulti s pl1) in H1.
  - destruct (MovePiece pl1 (-1, 0)%Z s) eqn: L1.
    + rewrite H1 in L1.
      exact (MovePieceGameoverMonotone L1 H2).
    + exact (FixPieceGameoverMonotone H1 H2).
  - discriminate H1.
Qed.

Lemma NewPieceYXStateGameoverUnchanged : ∀ [s pyxNew pl1] pl2,
  gameover (NewPieceYXState pyxNew pl1 s) pl2 = gameover s pl2.
Proof.
  intros; unfold gameover, NewPieceYXState, UnchangedT7Part; simpl.
  destruct (PlayerEqb pl2 pl1) eqn: L1; [ | reflexivity].
  apply PlayerEqbEq1 in L1; now rewrite L1.
Qed.

Lemma DropPieceGameoverMonotone : ∀ [s s' pl1 pl2 holes Hhole bagNew Hbag]
  (H1 : DropPiece pl1 holes Hhole bagNew Hbag s = Some s')
  (H2 : gameover s pl2 = true),
  gameover s' pl2 = true.
Proof.
  intros; unfold DropPiece in H1.
  apply (FixPieceGameoverMonotone H1).
  now rewrite (NewPieceYXStateGameoverUnchanged pl2).
Qed.

Lemma ReceiveMessageGameoverMonotone : ∀ [s s' pl1 pl2 from]
  (H1 : ReceiveMessage pl1 from s = Some s')
  (H2 : gameover s pl2 = true),
  gameover s' pl2 = true.
Proof.
  intros; unfold gameover in *; unfold ReceiveMessage in H1.
  destruct (connected s pl1) eqn: L1; [ | discriminate H1].
  destruct (messages s from pl1) as [|m ms] eqn: L2; [discriminate H1 |].
  destruct m; inject H1; now rewrite <- H1.
Qed.

Lemma DisconnectPlayerGameoverMonotone : ∀ [s s' pl1 pl2]
  (H1 : DisconnectPlayer pl1 s = Some s')
  (H2 : gameover s pl2 = true),
  gameover s' pl2 = true.
Proof.
  intros; unfold gameover in *; unfold DisconnectPlayer in H1.
  destruct (connected s pl1) eqn: L1; [ inject H1 | discriminate H1].
  now rewrite <- H1.
Qed.

Lemma NoticeDisconnectionGameoverMonotone : ∀ [s s' pl1 pl2]
  (H1 : NoticeDisconnection pl1 s = Some s')
  (H2 : gameover s pl2 = true),
  gameover s' pl2 = true.
Proof.
  intros; unfold gameover in *; unfold NoticeDisconnection in H1.
  destruct (! connected s pl1 && connectedView s pl1 pl1); [ inject H1 | discriminate H1].
  now rewrite <- H1.
Qed.

Theorem GameoverMonotoneHolds : ∀ s s', GameoverMonotone s s'.
Proof.
  intros s s' e pl1 pl2 H1 H2.
  unfold Next in H1; destruct e in H1; simpl in H1; (
    eapp MovePieceGameoverMonotone || eapp RotatePieceGameoverMonotone ||
    eapp FixPieceGameoverMonotone || eapp FallStepGameoverMonotone ||
    eapp HoldPieceGameoverMonotone || eapp DropPieceGameoverMonotone ||
    eapp RotateKickPieceGameoverMonotone || eapp ReceiveMessageGameoverMonotone ||
    eapp DisconnectPlayerGameoverMonotone || eapp NoticeDisconnectionGameoverMonotone ||
    (inject H1; now rewrite <- H1)).
Qed.


(* ========================================================================= *)
(* DisconnectedMonotone                                                      *)
(* ========================================================================= *)

Lemma GuardedUpdateConnectedMonotone : ∀ [A s s' pl1 pl2] [f : A → option T6.State] [x : A]
  (H1 : (if ! WinnerMulti s pl1 then option_map (UpdatePlayer s pl1) (f x) else None) = Some s')
  (H2 : connected s pl2 = false),
  connected s' pl2 = false.
Proof.
  (* sauto use: IfSome, T5P.OptionMapSome. *)
  intros.
  apply IfSome, T5P.OptionMapSome in H1.
  destruct H1 as [s6' [_ L1]]; now rewrite <- L1.
Qed.

Lemma MovePieceConnectedMonotone : ∀ [s s' pl1 pl2 dyx]
  (H1 : MovePiece pl1 dyx s = Some s')
  (H2 : connected s pl2 = false),
  connected s' pl2 = false.
Proof. intros; exact (GuardedUpdateConnectedMonotone H1 H2). Qed.

Lemma RotatePieceConnectedMonotone : ∀ [s s' pl1 pl2 dyx]
  (H1 : RotatePiece pl1 dyx s = Some s')
  (H2 : connected s pl2 = false),
  connected s' pl2 = false.
Proof. intros; exact (GuardedUpdateConnectedMonotone H1 H2). Qed.

Lemma HoldPieceConnectedMonotone : ∀ [s s' pl1 pl2 holes Hhole bagNew Hbag]
  (H1 : HoldPiece pl1 holes Hhole bagNew Hbag s = Some s')
  (H2 : connected s pl2 = false),
  connected s' pl2 = false.
Proof. intros; exact (GuardedUpdateConnectedMonotone H1 H2). Qed.

Lemma RotateKickPieceConnectedMonotone : ∀ [s s' pl1 pl2 cw]
  (H1 : RotateKickPiece pl1 cw s = Some s')
  (H2 : connected s pl2 = false),
  connected s' pl2 = false.
Proof. intros; exact (GuardedUpdateConnectedMonotone H1 H2). Qed.

Lemma FixPieceConnectedMonotone : ∀ [s s' pl1 pl2 holes Hhole bagNew Hbag]
  (H1 : FixPiece pl1 holes Hhole bagNew Hbag s = Some s')
  (H2 : connected s pl2 = false),
  connected s' pl2 = false.
Proof.
  intros; unfold FixPiece in H1.
  destruct (! WinnerMulti s pl1) eqn: L1; [ | discriminate H1].
  destruct (T6.FixPiece bagNew Hbag (s6 s pl1)) as [s6' |] eqn: L2; [ | discriminate H1].
  unfold option_map in H1; inject H1.
  destruct ((PlayerCount =? 1)%nat) eqn: L3; now rewrite <- H1.
Qed.

Lemma FallStepConnectedMonotone : ∀ [s s' pl1 pl2 holes Hhole bagNew Hbag]
  (H1 : FallStep pl1 holes Hhole bagNew Hbag s = Some s')
  (H2 : connected s pl2 = false),
  connected s' pl2 = false.
Proof.
  intros; unfold FallStep in H1.
  destruct (! WinnerMulti s pl1) in H1.
  - destruct (MovePiece pl1 (-1, 0)%Z s) eqn: L1.
    + rewrite H1 in L1.
      exact (MovePieceConnectedMonotone L1 H2).
    + exact (FixPieceConnectedMonotone H1 H2).
  - discriminate H1.
Qed.

Lemma NewPieceYXStateConnectedUnchanged : ∀ s pyxNew pl1,
  connected (NewPieceYXState pyxNew pl1 s) = connected s.
Proof. reflexivity. Qed.

Lemma DropPieceConnectedMonotone : ∀ [s s' pl1 pl2 holes Hhole bagNew Hbag]
  (H1 : DropPiece pl1 holes Hhole bagNew Hbag s = Some s')
  (H2 : connected s pl2 = false),
  connected s' pl2 = false.
Proof.
  intros; unfold DropPiece in H1.
  apply (FixPieceConnectedMonotone H1).
  now rewrite NewPieceYXStateConnectedUnchanged.
Qed.

Lemma ReceiveMessageConnectedMonotone : ∀ [s s' pl1 pl2 from]
  (H1 : ReceiveMessage pl1 from s = Some s')
  (H2 : connected s pl2 = false),
  connected s' pl2 = false.
Proof.
  intros; unfold ReceiveMessage in H1.
  destruct (connected s pl1) eqn: L1; [ | discriminate H1].
  destruct (messages s from pl1) as [|m ms] eqn: L2; [discriminate H1 |].
  destruct m; inject H1; now rewrite <- H1.
Qed.

Lemma NoticeDisconnectionConnectedMonotone : ∀ [s s' pl1 pl2]
  (H1 : NoticeDisconnection pl1 s = Some s')
  (H2 : connected s pl2 = false),
  connected s' pl2 = false.
Proof.
  intros; unfold NoticeDisconnection in H1.
  destruct (! connected s pl1 && connectedView s pl1 pl1); [ inject H1 | discriminate H1].
  now rewrite <- H1.
Qed.

Lemma DisconnectPlayerConnectedMonotone : ∀ [s s' pl1 pl2]
  (H1 : DisconnectPlayer pl1 s = Some s')
  (H2 : connected s pl2 = false),
  connected s' pl2 = false.
Proof.
  intros; unfold DisconnectPlayer in H1.
  destruct (connected s pl1) eqn: L1; [ inject H1 | discriminate H1].
  assert (L2 : connected s' = λ pl0,
      if PlayerEqb pl1 Host || PlayerEqb pl0 pl1 then false else connected s pl0)
    by now rewrite <- H1.
  rewrite L2.
  destruct (PlayerEqb pl1 Host || PlayerEqb pl2 pl1); [reflexivity | exact H2].
Qed.

Lemma StutterConnectedMonotone : ∀ [s s' pl]
  (H1 : Some s = Some s')
  (H2 : connected s pl = false),
  connected s' pl = false.
Proof. intros; inject H1; now rewrite <- H1. Qed.

Theorem DisconnectedMonotoneHolds : ∀ s s', DisconnectedMonotone s s'.
Proof.
  intros s s' e pl1 pl2 H1 H2.
  unfold Next in H1; destruct e in H1; simpl in H1; eauto using
    MovePieceConnectedMonotone, RotatePieceConnectedMonotone,
    FixPieceConnectedMonotone, FallStepConnectedMonotone,
    HoldPieceConnectedMonotone, DropPieceConnectedMonotone,
    RotateKickPieceConnectedMonotone, ReceiveMessageConnectedMonotone,
    DisconnectPlayerConnectedMonotone, NoticeDisconnectionConnectedMonotone,
    StutterConnectedMonotone.
Qed.


(* ========================================================================= *)
(* MessageSound                                                              *)
(* ========================================================================= *)

(* Init: all queues are empty, so both clauses are vacuous. *)
Lemma InitMessageSound : ∀ bags H, MessageSound (Init bags H).
Proof. intros bags H from to; simpl; split; intros []. Qed.

(* Move/Rotate/Hold/RotateKick (via UpdatePlayer): messages and connected are
untouched; gameover can move for the acting player, but GameoverMonotone
already covers that. *)
Lemma MovePieceMessageSound : ∀ [s s' pl1 dyx]
  (Hc : MessageSound s)
  (H1 : MovePiece pl1 dyx s = Some s'),
  MessageSound s'.
Proof.
  intros.
  assert (H1' := H1); apply IfSome, T5P.OptionMapSome in H1'.
  destruct H1' as [s6' [_ E2]].
  assert (Hmsg : messages s' = messages s) by now rewrite <- E2.
  assert (Hconn : connected s' = connected s) by now rewrite <- E2.
  intros from to; split; intros Hin; rewrite Hmsg in Hin.
  - exact (MovePieceGameoverMonotone H1 (proj1 (Hc from to) Hin)).
  - rewrite Hconn; exact (proj2 (Hc from to) Hin).
Qed.

Lemma RotatePieceMessageSound : ∀ [s s' pl1 dyx]
  (Hc : MessageSound s)
  (H1 : RotatePiece pl1 dyx s = Some s'),
  MessageSound s'.
Proof.
  intros.
  assert (H1' := H1); apply IfSome, T5P.OptionMapSome in H1'.
  destruct H1' as [s6' [_ E2]].
  assert (Hmsg : messages s' = messages s) by now rewrite <- E2.
  assert (Hconn : connected s' = connected s) by now rewrite <- E2.
  intros from to; split; intros Hin; rewrite Hmsg in Hin.
  - exact (RotatePieceGameoverMonotone H1 (proj1 (Hc from to) Hin)).
  - rewrite Hconn; exact (proj2 (Hc from to) Hin).
Qed.

Lemma HoldPieceMessageSound : ∀ [s s' pl1 holes Hhole bagNew Hbag]
  (Hc : MessageSound s)
  (H1 : HoldPiece pl1 holes Hhole bagNew Hbag s = Some s'),
  MessageSound s'.
Proof.
  intros.
  assert (H1' := H1); apply IfSome, T5P.OptionMapSome in H1'.
  destruct H1' as [s6' [_ E2]].
  assert (Hmsg : messages s' = messages s) by now rewrite <- E2.
  assert (Hconn : connected s' = connected s) by now rewrite <- E2.
  intros from to; split; intros Hin; rewrite Hmsg in Hin.
  - exact (HoldPieceGameoverMonotone H1 (proj1 (Hc from to) Hin)).
  - rewrite Hconn; exact (proj2 (Hc from to) Hin).
Qed.

Lemma RotateKickPieceMessageSound : ∀ [s s' pl1 cw]
  (Hc : MessageSound s)
  (H1 : RotateKickPiece pl1 cw s = Some s'),
  MessageSound s'.
Proof.
  intros.
  assert (H1' := H1); apply IfSome, T5P.OptionMapSome in H1'.
  destruct H1' as [s6' [_ E2]].
  assert (Hmsg : messages s' = messages s) by now rewrite <- E2.
  assert (Hconn : connected s' = connected s) by now rewrite <- E2.
  intros from to; split; intros Hin; rewrite Hmsg in Hin.
  - exact (RotateKickPieceGameoverMonotone H1 (proj1 (Hc from to) Hin)).
  - rewrite Hconn; exact (proj2 (Hc from to) Hin).
Qed.

(* FixPiece: the only op that ever appends to a queue. It appends only to
(from := pl1, to <> pl1), only when connected s pl1, and only a GarbageMessage
and/or a GameoverMessage, never a DisconnectMessage. A freshly appended
GameoverMessage is sound by construction (NewMainGridGameoverStateGameover);
anything already in the queue is handled the same way as every other op, via
FixPieceGameoverMonotone / connected being untouched. *)
Lemma FixPieceMessageSound : ∀ [s s' pl1 holes Hhole bagNew Hbag]
  (Hc : MessageSound s)
  (H1 : FixPiece pl1 holes Hhole bagNew Hbag s = Some s'),
  MessageSound s'.
Proof.
  intros.
  assert (H1' := H1); unfold FixPiece in H1'.
  destruct (! WinnerMulti s pl1) eqn: L1; [ | discriminate H1'].
  destruct (T6.FixPiece bagNew Hbag (s6 s pl1)) as [s6' |] eqn: L2; [ | discriminate H1'].
  unfold option_map in H1'; inject H1'.
  assert (Hconn : connected s' = connected s). {
    rewrite <- H1'; destruct ((PlayerCount =? 1)%nat); reflexivity.
  }
  destruct ((PlayerCount =? 1)%nat) eqn: L3.
  - assert (Hmsg : messages s' = messages s) by now rewrite <- H1'.
    intros from to; split; intros Hin; rewrite Hmsg in Hin.
    + exact (FixPieceGameoverMonotone H1 (proj1 (Hc from to) Hin)).
    + rewrite Hconn; exact (proj2 (Hc from to) Hin).
  - set (gameover' := FP.Gameover' s pl1 s6' holes) in *.
    set (remGenGarbage := FP.RemGenGarbage s pl1 s6') in *.
    assert (Hmsg : ∀ from to, messages s' from to =
        if connected s pl1 && PlayerEqb from pl1 && ! PlayerEqb to pl1
        then messages s from to
               ++ (if PlayerEqb to (target s pl1) && (0 <? remGenGarbage)%nat
                   then [GarbageMessage remGenGarbage] else [])
               ++ (if gameover' then [GameoverMessage] else [])
        else messages s from to). {
      intros from to; rewrite <- H1'; unfold SendMessages; simpl.
      destruct (connected s pl1) eqn: Lc; [ | reflexivity].
      destruct (PlayerEqb from pl1) eqn: Lf; [ | reflexivity].
      destruct (PlayerEqb to pl1) eqn: Lt; reflexivity.
    }
    assert (Hgover : ∀ to,
        In GameoverMessage
          ((if PlayerEqb to (target s pl1) && (0 <? remGenGarbage)%nat
            then [GarbageMessage remGenGarbage] else [])
           ++ (if gameover' then [GameoverMessage] else []))
        → gameover' = true). {
      intros to Hin.
      apply in_app_or in Hin as [Hin | Hin].
      - destruct (PlayerEqb to (target s pl1) && (0 <? remGenGarbage)%nat) eqn: Lguard;
          simpl in Hin.
        + destruct Hin as [Heq | []]; discriminate Heq.
        + destruct Hin.
      - destruct gameover' eqn: Hg; simpl in Hin.
        + reflexivity.
        + destruct Hin.
    }
    assert (Hnodisc : ∀ to,
        In DisconnectMessage
          ((if PlayerEqb to (target s pl1) && (0 <? remGenGarbage)%nat
            then [GarbageMessage remGenGarbage] else [])
           ++ (if gameover' then [GameoverMessage] else []))
        → False). {
      intros to Hin.
      apply in_app_or in Hin as [Hin | Hin].
      - destruct (PlayerEqb to (target s pl1) && (0 <? remGenGarbage)%nat) eqn: Lguard;
          simpl in Hin.
        + destruct Hin as [Heq | []]; discriminate Heq.
        + destruct Hin.
      - destruct gameover' eqn: Hg; simpl in Hin.
        + destruct Hin as [Heq | []]; discriminate Heq.
        + destruct Hin.
    }
    intros from to; split; intros Hin; rewrite (Hmsg from to) in Hin.
    + destruct (connected s pl1 && PlayerEqb from pl1 && ! PlayerEqb to pl1) eqn: Lg.
      * apply in_app_or in Hin as [Hin | Hin].
        -- exact (FixPieceGameoverMonotone H1 (proj1 (Hc from to) Hin)).
        -- apply andb_true_iff in Lg as [Lg1 _]; apply andb_true_iff in Lg1 as [_ Lg1b].
           apply PlayerEqbEq1 in Lg1b.
           assert (Hg' : gameover' = true) by exact (Hgover to Hin).
           unfold gameover; rewrite <- H1'; simpl; rewrite Lg1b, PlayerEqbReflexive.
           rewrite (NewMainGridGameoverStateGameover
                      (FP.CroppedMg' s pl1 s6' holes) gameover' s6').
           exact Hg'.
      * exact (FixPieceGameoverMonotone H1 (proj1 (Hc from to) Hin)).
    + destruct (connected s pl1 && PlayerEqb from pl1 && ! PlayerEqb to pl1) eqn: Lg.
      * rewrite Hconn.
        apply in_app_or in Hin as [Hin | Hin].
        -- exact (proj2 (Hc from to) Hin).
        -- destruct (Hnodisc to Hin).
      * rewrite Hconn; exact (proj2 (Hc from to) Hin).
Qed.

(* Forward to MovePiece / FixPiece, same as for the other invariants. *)
Lemma FallStepMessageSound : ∀ [s s' pl1 holes Hhole bagNew Hbag]
  (Hc : MessageSound s)
  (H1 : FallStep pl1 holes Hhole bagNew Hbag s = Some s'),
  MessageSound s'.
Proof.
  intros; unfold FallStep in H1.
  destruct (! WinnerMulti s pl1) in H1.
  - destruct (MovePiece pl1 (-1, 0)%Z s) eqn: L1.
    + rewrite H1 in L1.
      exact (MovePieceMessageSound Hc L1).
    + exact (FixPieceMessageSound Hc H1).
  - discriminate H1.
Qed.

(* NewPieceYXState doesn't touch messages/gameover/connected at all. *)
Lemma NewPieceYXStateMessageSound : ∀ [s pyxNew pl1]
  (Hc : MessageSound s),
  MessageSound (NewPieceYXState pyxNew pl1 s).
Proof.
  intros; split; intros Hin.
  - rewrite (NewPieceYXStateGameoverUnchanged from).
    apply (Hc from to); exact Hin.
  - rewrite NewPieceYXStateConnectedUnchanged. apply (Hc from to); exact Hin.
Qed.

Lemma DropPieceMessageSound : ∀ [s s' pl1 holes Hhole bagNew Hbag]
  (Hc : MessageSound s)
  (H1 : DropPiece pl1 holes Hhole bagNew Hbag s = Some s'),
  MessageSound s'.
Proof.
  intros; unfold DropPiece in H1.
  exact (FixPieceMessageSound (NewPieceYXStateMessageSound Hc) H1).
Qed.

(* ReceiveMessage: only ever shrinks one queue (pops its head); s6 and
connected are untouched. *)
Lemma ReceiveMessageMessageSound : ∀ [s s' pl msgFrom]
  (Hc : MessageSound s)
  (H1 : ReceiveMessage pl msgFrom s = Some s'),
  MessageSound s'.
Proof.
  intros; unfold ReceiveMessage in H1.
  destruct (connected s pl) eqn: L1; [ | discriminate H1].
  destruct (messages s msgFrom pl) as [|m ms] eqn: L2; [discriminate H1 |].
  assert (Hs6 : s6 s' = s6 s) by (destruct m; inject H1; now rewrite <- H1).
  assert (Hconn : connected s' = connected s) by (destruct m; inject H1; now rewrite <- H1).
  assert (Hgo : ∀ pl2, gameover s' pl2 = gameover s pl2)
    by (intro; unfold gameover; now rewrite Hs6).
  assert (Hco : ∀ pl2, connected s' pl2 = connected s pl2)
    by (intro; now rewrite Hconn).
  assert (Hmsg : ∀ from to, messages s' from to =
      if PlayerEqb from msgFrom && PlayerEqb to pl then ms else messages s from to)
    by (intros; destruct m; inject H1; now rewrite <- H1).
  intros from to; split.
  - intros Hin; rewrite (Hmsg from to) in Hin.
    destruct (PlayerEqb from msgFrom && PlayerEqb to pl) eqn: Lft.
    + apply andb_true_iff in Lft as [Lf _]; apply PlayerEqbEq1 in Lf.
      assert (Hin' : In GameoverMessage (messages s msgFrom pl))
        by (rewrite L2; right; exact Hin).
      rewrite Hgo, Lf; exact (proj1 (Hc msgFrom pl) Hin').
    + rewrite Hgo; exact (proj1 (Hc from to) Hin).
  - intros Hin; rewrite (Hmsg from to) in Hin.
    destruct (PlayerEqb from msgFrom && PlayerEqb to pl) eqn: Lft.
    + apply andb_true_iff in Lft as [Lf _]; apply PlayerEqbEq1 in Lf.
      assert (Hin' : In DisconnectMessage (messages s msgFrom pl))
        by (rewrite L2; right; exact Hin).
      rewrite Hco, Lf; exact (proj2 (Hc msgFrom pl) Hin').
    + rewrite Hco; exact (proj2 (Hc from to) Hin).
Qed.

(* DisconnectPlayer: the only op that ever appends a DisconnectMessage — to
every (from := pl, to <> pl); s6 is untouched, so gameover is unaffected. *)
Lemma DisconnectPlayerMessageSound : ∀ [s s' pl]
  (Hc : MessageSound s)
  (H1 : DisconnectPlayer pl s = Some s'),
  MessageSound s'.
Proof.
  intros; unfold DisconnectPlayer in H1.
  destruct (connected s pl) eqn: L1; [ inject H1 | discriminate H1].
  assert (Hs6 : s6 s' = s6 s) by now rewrite <- H1.
  assert (Hconn : connected s' = λ pl1,
      if PlayerEqb pl Host || PlayerEqb pl1 pl then false else connected s pl1)
    by now rewrite <- H1.
  assert (Hmsg : ∀ from to, messages s' from to =
      if ! PlayerEqb pl Host && PlayerEqb from pl && ! PlayerEqb to pl
      then messages s from to ++ [DisconnectMessage] else messages s from to)
    by (intros; now rewrite <- H1).
  assert (Hgo : ∀ pl2, gameover s' pl2 = gameover s pl2)
    by (intro; unfold gameover; now rewrite Hs6).
  intros from to; split.
  - intros Hin; rewrite (Hmsg from to) in Hin.
    destruct (! PlayerEqb pl Host && PlayerEqb from pl && ! PlayerEqb to pl) eqn: Lg.
    + apply in_app_or in Hin as [Hin | Hin].
      * rewrite Hgo; exact (proj1 (Hc from to) Hin).
      * destruct Hin as [Heq | []]; discriminate Heq.
    + rewrite Hgo; exact (proj1 (Hc from to) Hin).
  - intros Hin; rewrite (Hmsg from to) in Hin.
    destruct (! PlayerEqb pl Host && PlayerEqb from pl && ! PlayerEqb to pl) eqn: Lg.
    + apply andb_true_iff in Lg as [Lg1 _]; apply andb_true_iff in Lg1 as [_ Lg1b].
      rewrite Hconn, Lg1b, orb_true_r; reflexivity.
    + rewrite Hconn.
      destruct ((pl =? Host) || (from =? pl))%player.
      -- reflexivity.
      -- exact (proj2 (Hc from to) Hin).
Qed.

(* NoticeDisconnection: messages, s6 and connected are all untouched (only
connectedView moves). *)
Lemma NoticeDisconnectionMessageSound : ∀ [s s' pl]
  (Hc : MessageSound s)
  (H1 : NoticeDisconnection pl s = Some s'),
  MessageSound s'.
Proof.
  intros; unfold NoticeDisconnection in H1.
  destruct (! connected s pl && connectedView s pl pl); [ inject H1 | discriminate H1].
  intros from to; rewrite <- H1; exact (Hc from to).
Qed.

Theorem SpecMessageSound :
   (∀ bags H, MessageSound (Init bags H))
 ∧ (∀ [pl e s s']
      (Hc : MessageSound s)
      (H1 : Next pl e s = Some s'),
      MessageSound s').
Proof.
  split.
  - exact InitMessageSound.
  - intros pl e s s' Hc H1.
    unfold Next in H1; destruct e in H1; simpl in H1; (
      eapp MovePieceMessageSound || eapp RotatePieceMessageSound ||
      eapp FixPieceMessageSound || eapp FallStepMessageSound ||
      eapp HoldPieceMessageSound || eapp DropPieceMessageSound ||
      eapp RotateKickPieceMessageSound || eapp ReceiveMessageMessageSound ||
      eapp DisconnectPlayerMessageSound || eapp NoticeDisconnectionMessageSound ||
      (inject H1; intros from to; rewrite <- H1; exact (Hc from to))).
Qed.

(* ========================================================================= *)
(* ViewSound                                                                 *)
(* ========================================================================= *)

(* Init: gameoverView pl pl reads pl's own real gameover status (everything
else defaults to false, vacuously sound); connectedView is a constant equal
to connected. *)
Lemma InitViewSound : ∀ bags H, ViewSound (Init bags H).
Proof.
  intros bags H pl pl2; split; intros Hin.
  - simpl in Hin.
    destruct (PlayerEqb pl2 pl) eqn: Lc; [ | discriminate Hin].
    unfold gameover; simpl; exact Hin.
  - simpl in Hin; simpl; exact Hin.
Qed.

(* Move/Rotate/Hold/RotateKick (via UpdatePlayer) and FixPiece's own view of
herself: same reasoning as SelfViewAccurate's PointUpdateSelfViewAccurate.
What's new here is another player's already-sound view of the acting player,
which GameoverMonotone (Hgm) carries across the step. *)
Section Player.
Open Scope player_scope.

Lemma PointUpdateViewSound : ∀ [s s' pl1 s6new]
  (H1 : ViewSound s)
  (H2 : s6 s' = λ pl2, if pl2 =? pl1 then s6new else s6 s pl2)
  (H3 : gameoverView s' = λ obs obsd,
      if (obs =? pl1) && (obsd =? pl1) then T6.gameover s6new else gameoverView s obs obsd)
  (H4 : connectedView s' = connectedView s)
  (H5 : connected s' = connected s)
  (Hgm : ∀ pl2, gameover s pl2 = true → gameover s' pl2 = true),
  ViewSound s'.
Proof.
  intros; split; intros Hin.
  - rewrite H3 in Hin.
    destruct ((pl =? pl1) && (pl2 =? pl1)) eqn: Lc.
    + apply andb_true_iff in Lc as [_ Lc2]; apply PlayerEqbEq1 in Lc2.
      unfold gameover; rewrite H2, Lc2, PlayerEqbReflexive.
      exact Hin.
    + exact (Hgm pl2 (proj1 (H1 pl pl2) Hin)).
  - rewrite H4 in Hin; rewrite H5.
    exact (proj2 (H1 pl pl2) Hin).
Qed.

Lemma UpdatePlayerPreservesViewSound : ∀ [s s' pl1 s6']
  (H1 : ViewSound s)
  (H2 : UpdatePlayer s pl1 s6' = s')
  (Hgm : ∀ pl2, gameover s pl2 = true → gameover s' pl2 = true),
  ViewSound s'.
Proof.
  intros.
  apply (@PointUpdateViewSound s s' pl1 s6' H1); try (now rewrite <- H2).
  exact Hgm.
Qed.

End Player.

Lemma GuardedUpdateViewSound : ∀ [A s s' pl1] [f : A → option T6.State] [x : A]
  (H1 : ViewSound s)
  (H2 : (if ! WinnerMulti s pl1 then option_map (UpdatePlayer s pl1) (f x) else None) = Some s')
  (Hgm : ∀ pl2, gameover s pl2 = true → gameover s' pl2 = true),
  ViewSound s'.
Proof.
  intros.
  apply IfSome, T5P.OptionMapSome in H2.
  destruct H2 as [s6' [_ L1]].
  exact (UpdatePlayerPreservesViewSound H1 L1 Hgm).
Qed.

(* Lemma MovePieceGameoverMonotone : ∀ [s s' pl1 pl2 dyx]
  (H1 : MovePiece pl1 dyx s = Some s')
  (H2 : gameover s pl2 = true),
  gameover s' pl2 = true. *)

Lemma MovePieceViewSound : ∀ [s s' pl dyx]
  (H1 : ViewSound s)
  (H2 : MovePiece pl dyx s = Some s'),
  ViewSound s'.
Proof.
  intros; apply (GuardedUpdateViewSound H1 H2).
  now intros; apply (MovePieceGameoverMonotone H2).
Qed.

Lemma RotatePieceViewSound : ∀ [s s' pl dyx]
  (H1 : ViewSound s)
  (H2 : RotatePiece pl dyx s = Some s'),
  ViewSound s'.
Proof.
  intros; apply (GuardedUpdateViewSound H1 H2).
  now intros; apply (RotatePieceGameoverMonotone H2).
Qed.

Lemma HoldPieceViewSound : ∀ [s s' pl holes Hhole bagNew Hbag]
  (H1 : ViewSound s)
  (H2 : HoldPiece pl holes Hhole bagNew Hbag s = Some s'),
  ViewSound s'.
Proof.
  intros; apply (GuardedUpdateViewSound H1 H2).
  now intros; apply (HoldPieceGameoverMonotone H2).
Qed.

Lemma RotateKickPieceViewSound : ∀ [s s' pl cw]
  (H1 : ViewSound s)
  (H2 : RotateKickPiece pl cw s = Some s'),
  ViewSound s'.
Proof.
  intros; apply (GuardedUpdateViewSound H1 H2).
  now intros; apply (RotateKickPieceGameoverMonotone H2).
Qed.

Section Player.
Open Scope player_scope.

Lemma FixPieceViewSound : ∀ [s s' pl holes Hhole bagNew Hbag]
  (H1 : ViewSound s)
  (H2 : FixPiece pl holes Hhole bagNew Hbag s = Some s'),
  ViewSound s'.
Proof.
  intros.
  assert (H2' := H2); unfold FixPiece in H2'.
  destruct (! WinnerMulti s pl) eqn: L1; [ | discriminate H2'].
  destruct (T6.FixPiece bagNew Hbag (s6 s pl)) as [s6' |] eqn: L2; [ | discriminate H2'].
  unfold option_map in H2'; inject H2'.
  destruct ((PlayerCount =? 1)%nat) eqn: L3.
  - apply (UpdatePlayerPreservesViewSound H1 H2').
    now intros; apply (FixPieceGameoverMonotone H2).
  - assert (L3_1 : s6 s' = λ pl2, if pl2 =? pl then
        NewMainGridGameoverState (FP.CroppedMg' s pl s6' holes) (FP.Gameover' s pl s6' holes) s6'
        else s6 s pl2)
      by now rewrite <- H2'.
    assert (L3_2 : gameoverView s' = λ obs obsd,
        if (obs =? pl) && (obsd =? pl) then
          T6.gameover (NewMainGridGameoverState (FP.CroppedMg' s pl s6' holes)
                         (FP.Gameover' s pl s6' holes) s6')
        else gameoverView s obs obsd)
      by now rewrite <- H2'.
    assert (L3_3 : connectedView s' = connectedView s) by now rewrite <- H2'.
    assert (L3_4 : connected s' = connected s) by now rewrite <- H2'.
    apply (PointUpdateViewSound H1 L3_1 L3_2 L3_3 L3_4).
    now intros; apply (FixPieceGameoverMonotone H2).
Qed.

End Player.

(* Forward to MovePiece and FixPiece, same as for the other invariants. *)
Lemma FallStepViewSound : ∀ [s s' pl holes Hhole bagNew Hbag]
  (H1 : ViewSound s)
  (H2 : FallStep pl holes Hhole bagNew Hbag s = Some s'),
  ViewSound s'.
Proof.
  intros; unfold FallStep in H2.
  destruct (! WinnerMulti s pl) in H2.
  - destruct (MovePiece pl (-1, 0)%Z s) eqn: L1.
    + rewrite H2 in L1; apply (MovePieceViewSound H1 L1).
    + apply (FixPieceViewSound H1 H2).
  - discriminate H2.
Qed.

(* NewPieceYXState doesn't touch gameoverView/connectedView/connected at all,
and leaves gameover unchanged (NewPieceYXStateGameoverUnchanged). *)
Lemma NewPieceYXStateViewSound : ∀ [s pyxNew pl1]
  (H1 : ViewSound s),
  ViewSound (NewPieceYXState pyxNew pl1 s).
Proof.
  intros; split; intros Hin.
  - rewrite (NewPieceYXStateGameoverUnchanged pl2).
    exact (proj1 (H1 pl pl2) Hin).
  - exact (proj2 (H1 pl pl2) Hin).
Qed.

Lemma DropPieceViewSound : ∀ [s s' pl holes Hhole bagNew Hbag]
  (H1 : ViewSound s)
  (H2 : DropPiece pl holes Hhole bagNew Hbag s = Some s'),
  ViewSound s'.
Proof.
  intros; unfold DropPiece in H2.
  exact (FixPieceViewSound (NewPieceYXStateViewSound H1) H2).
Qed.

(* ReceiveMessage, GarbageMessage branch: gameoverView, connectedView and
connected are all untouched. *)
Lemma UnchangedViewSound : ∀ [s s']
  (H1 : ViewSound s)
  (H2 : s6 s' = s6 s)
  (H3 : gameoverView s' = gameoverView s)
  (H4 : connectedView s' = connectedView s)
  (H5 : connected s' = connected s),
  ViewSound s'.
Proof.
  intros; split; intros Hin.
  - rewrite H3 in Hin; unfold gameover; rewrite H2.
    exact (proj1 (H1 pl pl2) Hin).
  - rewrite H4 in Hin; rewrite H5.
    exact (proj2 (H1 pl pl2) Hin).
Qed.

(* ReceiveMessage, GameoverMessage branch: pl's belief that msgFrom is gameover
is set to true. MessageSound guarantees the message wasn't lying. *)
Lemma ReceiveGameoverMessageViewSound : ∀ [s s' pl msgFrom ms]
  (H1 : ViewSound s)
  (Hms : MessageSound s)
  (H3 : messages s msgFrom pl = GameoverMessage :: ms)
  (Hs : s6 s' = s6 s)
  (Hg : gameoverView s' = λ obs obsd,
      if PlayerEqb obs pl && PlayerEqb obsd msgFrom then true else gameoverView s obs obsd)
  (Hcv : connectedView s' = connectedView s)
  (Hc : connected s' = connected s),
  ViewSound s'.
Proof.
  intros; split; intros Hin.
  - rewrite Hg in Hin.
    destruct (PlayerEqb pl0 pl && PlayerEqb pl2 msgFrom) eqn: Lc.
    + apply andb_true_iff in Lc as [_ Lc2]; apply PlayerEqbEq1 in Lc2.
      unfold gameover; rewrite Hs, Lc2.
      apply (proj1 (Hms msgFrom pl)).
      rewrite H3; left; reflexivity.
    + unfold gameover; rewrite Hs.
      exact (proj1 (H1 pl0 pl2) Hin).
  - rewrite Hcv in Hin; rewrite Hc.
    exact (proj2 (H1 pl0 pl2) Hin).
Qed.

(* ReceiveMessage, DisconnectMessage branch: symmetric to the GameoverMessage
case, on the connectedView/connected clause instead. *)
Lemma ReceiveDisconnectMessageViewSound : ∀ [s s' pl msgFrom ms]
  (H1 : ViewSound s)
  (Hms : MessageSound s)
  (H3 : messages s msgFrom pl = DisconnectMessage :: ms)
  (Hs : s6 s' = s6 s)
  (Hg : gameoverView s' = gameoverView s)
  (Hcv : connectedView s' = λ obs obsd,
      if PlayerEqb obs pl && PlayerEqb obsd msgFrom then false else connectedView s obs obsd)
  (Hc : connected s' = connected s),
  ViewSound s'.
Proof.
  intros; split; intros Hin.
  - rewrite Hg in Hin; unfold gameover; rewrite Hs.
    exact (proj1 (H1 pl0 pl2) Hin).
  - rewrite Hcv in Hin.
    destruct (PlayerEqb pl0 pl && PlayerEqb pl2 msgFrom) eqn: Lc.
    + apply andb_true_iff in Lc as [_ Lc2]; apply PlayerEqbEq1 in Lc2.
      rewrite Hc, Lc2.
      apply (proj2 (Hms msgFrom pl)).
      rewrite H3; left; reflexivity.
    + rewrite Hc.
      exact (proj2 (H1 pl0 pl2) Hin).
Qed.

Lemma ReceiveMessageViewSound : ∀ [s s' pl msgFrom]
  (H1 : ViewSound s)
  (Hms : MessageSound s)
  (H3 : ReceiveMessage pl msgFrom s = Some s'),
  ViewSound s'.
Proof.
  intros.
  unfold ReceiveMessage in H3.
  destruct (connected s pl) eqn: L1; [ | discriminate H3].
  destruct (messages s msgFrom pl) as [|m ms] eqn: L2; [discriminate H3 |].
  destruct m as [n| |] eqn: L3.
  - inject H3.
    assert (L3_1 : s6 s' = s6 s) by now rewrite <- H3.
    assert (L3_2 : gameoverView s' = gameoverView s) by now rewrite <- H3.
    assert (L3_3 : connectedView s' = connectedView s) by now rewrite <- H3.
    assert (L3_4 : connected s' = connected s) by now rewrite <- H3.
    exact (UnchangedViewSound H1 L3_1 L3_2 L3_3 L3_4).
  - inject H3.
    assert (L3_1 : s6 s' = s6 s) by now rewrite <- H3.
    assert (L3_2 : gameoverView s' = λ obs obsd,
        if PlayerEqb obs pl && PlayerEqb obsd msgFrom then true else gameoverView s obs obsd)
      by now rewrite <- H3.
    assert (L3_3 : connectedView s' = connectedView s) by now rewrite <- H3.
    assert (L3_4 : connected s' = connected s) by now rewrite <- H3.
    exact (ReceiveGameoverMessageViewSound H1 Hms L2 L3_1 L3_2 L3_3 L3_4).
  - inject H3.
    assert (L3_1 : s6 s' = s6 s) by now rewrite <- H3.
    assert (L3_2 : gameoverView s' = gameoverView s) by now rewrite <- H3.
    assert (L3_3 : connectedView s' = λ obs obsd,
        if PlayerEqb obs pl && PlayerEqb obsd msgFrom then false else connectedView s obs obsd)
      by now rewrite <- H3.
    assert (L3_4 : connected s' = connected s) by now rewrite <- H3.
    exact (ReceiveDisconnectMessageViewSound H1 Hms L2 L3_1 L3_2 L3_3 L3_4).
Qed.

(* DisconnectPlayer: connectedView is untouched, but connected itself can turn
more players' status false; DisconnectedMonotone carries an already-sound
view across the step, same role GameoverMonotone plays for the piece ops. *)
Lemma DisconnectPlayerViewSound : ∀ [s s' pl]
  (H1 : ViewSound s)
  (H2 : DisconnectPlayer pl s = Some s'),
  ViewSound s'.
Proof.
  intros.
  assert (L0 : DisconnectPlayer pl s = Some s') by exact H2. (* remember *)
  unfold DisconnectPlayer in H2.
  destruct (connected s pl) eqn: L1; [ inject H2 | discriminate H2].
  assert (L2_1 : s6 s' = s6 s) by now rewrite <- H2.
  assert (L2_2 : gameoverView s' = gameoverView s) by now rewrite <- H2.
  assert (L2_3 : connectedView s' = connectedView s) by now rewrite <- H2.
  intros pl0 pl2; split; intros Hin.
  - rewrite L2_2 in Hin; unfold gameover; rewrite L2_1.
    exact (proj1 (H1 pl0 pl2) Hin).
  - rewrite L2_3 in Hin.
    exact (DisconnectPlayerConnectedMonotone L0 (proj2 (H1 pl0 pl2) Hin)).
Qed.

(* NoticeDisconnection sets pl's own connectedView to false, matching what the
guard already asserts about her real connection status; every other entry is
untouched. *)
Lemma NoticeDisconnectionViewSound : ∀ [s s' pl]
  (H1 : ViewSound s)
  (H2 : NoticeDisconnection pl s = Some s'),
  ViewSound s'.
Proof.
  intros; unfold NoticeDisconnection in H2.
  destruct (! connected s pl && connectedView s pl pl) eqn: L1; [ inject H2 | discriminate H2].
  apply andb_true_iff in L1 as [L1a _]; apply negb_true_iff in L1a.
  assert (L2_1 : s6 s' = s6 s) by now rewrite <- H2.
  assert (L2_2 : gameoverView s' = gameoverView s) by now rewrite <- H2.
  assert (L2_3 : connectedView s' = λ pl1 pl2,
      if PlayerEqb pl1 pl && PlayerEqb pl2 pl then false else connectedView s pl1 pl2)
    by now rewrite <- H2.
  assert (L2_4 : connected s' = connected s) by now rewrite <- H2.
  intros pl0 pl2; split; intros Hin.
  - rewrite L2_2 in Hin; unfold gameover; rewrite L2_1.
    exact (proj1 (H1 pl0 pl2) Hin).
  - rewrite L2_3 in Hin.
    destruct (PlayerEqb pl0 pl && PlayerEqb pl2 pl) eqn: Lc.
    + apply andb_true_iff in Lc as [_ Lc2]; apply PlayerEqbEq1 in Lc2.
      rewrite L2_4, Lc2; exact L1a.
    + rewrite L2_4.
      exact (proj2 (H1 pl0 pl2) Hin).
Qed.

Lemma StutterViewSound : ∀ [s s']
  (H1 : ViewSound s)
  (H2 : Some s = Some s'),
  ViewSound s'.
Proof. intros; inject H2; now rewrite <- H2. Qed.

Lemma NextViewSound : ∀ [pl e s s']
  (H1 : ViewSound s)
  (Hms : MessageSound s)
  (H3 : Next pl e s = Some s'),
  ViewSound s'.
Proof.
  intros.
  destruct e in H3; simpl in H3; (
    eapp MovePieceViewSound || eapp RotatePieceViewSound ||
    eapp FixPieceViewSound || eapp FallStepViewSound ||
    eapp HoldPieceViewSound || eapp DropPieceViewSound ||
    eapp RotateKickPieceViewSound || eapp ReceiveMessageViewSound ||
    eapp DisconnectPlayerViewSound || eapp NoticeDisconnectionViewSound ||
    eapp StutterViewSound).
Qed.

Theorem SpecViewSound :
   (∀ bags H, ViewSound (Init bags H))
 ∧ (∀ [pl e s s']
      (H1 : ViewSound s)
      (H2 : MessageSound s)
      (H3 : Next pl e s = Some s'),
      ViewSound s').
Proof. split; (exact InitViewSound || exact NextViewSound). Qed.


(* ========================================================================= *)
(* NoSelfMessage                                                             *)
(* ========================================================================= *)

(* Init: all queues start empty. *)
Lemma InitNoSelfMessage : ∀ bags H,
  NoSelfMessage (Init bags H).
Proof. sauto. Qed.

(* Move/Rotate/Hold/RotateKick (via UpdatePlayer): messages untouched. *)
Lemma GuardedUpdateNoSelfMessage : ∀ [A s s' pl1] [f : A → option T6.State] [x : A]
  (H1 : NoSelfMessage s)
  (H2 : (if ! WinnerMulti s pl1 then option_map (UpdatePlayer s pl1) (f x) else None) = Some s'),
  NoSelfMessage s'.
Proof.
  intros.
  apply IfSome, T5P.OptionMapSome in H2.
  destruct H2 as [s6' [_ E2]].
  intro pl; rewrite <- E2; exact (H1 pl).
Qed.

Lemma MovePieceNoSelfMessage : ∀ [s s' pl1 dyx]
  (H1 : NoSelfMessage s)
  (H2 : MovePiece pl1 dyx s = Some s'),
  NoSelfMessage s'.
Proof. intros; exact (GuardedUpdateNoSelfMessage H1 H2). Qed.

Lemma RotatePieceNoSelfMessage : ∀ [s s' pl1 dyx]
  (H1 : NoSelfMessage s)
  (H2 : RotatePiece pl1 dyx s = Some s'),
  NoSelfMessage s'.
Proof. intros; exact (GuardedUpdateNoSelfMessage H1 H2). Qed.

Lemma HoldPieceNoSelfMessage : ∀ [s s' pl1 holes Hhole bagNew Hbag]
  (H1 : NoSelfMessage s)
  (H2 : HoldPiece pl1 holes Hhole bagNew Hbag s = Some s'),
  NoSelfMessage s'.
Proof. intros; exact (GuardedUpdateNoSelfMessage H1 H2). Qed.

Lemma RotateKickPieceNoSelfMessage : ∀ [s s' pl1 cw]
  (H1 : NoSelfMessage s)
  (H2 : RotateKickPiece pl1 cw s = Some s'),
  NoSelfMessage s'.
Proof. intros; exact (GuardedUpdateNoSelfMessage H1 H2). Qed.

(* FixPiece: single-player branch is UpdatePlayer again (messages untouched).
Multiplayer: SendMessages's own guard (`!(from=?pl1)` then `to=?pl1`) makes
the append unreachable for a (pl,pl) query (both checks land on the same
boolean either way, so it always falls through to "unchanged"). *)
Lemma FixPieceNoSelfMessage : ∀ [s s' pl1 holes Hhole bagNew Hbag]
  (H1 : NoSelfMessage s)
  (H2 : FixPiece pl1 holes Hhole bagNew Hbag s = Some s'),
  NoSelfMessage s'.
Proof.
  intros.
  unfold FixPiece in H2.
  destruct (! WinnerMulti s pl1) eqn: L1; [ | discriminate H2].
  destruct (T6.FixPiece bagNew Hbag (s6 s pl1)) as [s6' |] eqn: L2; [ | discriminate H2].
  unfold option_map in H2; inject H2.
  destruct ((PlayerCount =? 1)%nat) eqn: L3.
  - intro pl; rewrite <- H2; exact (H1 pl).
  - intro pl; rewrite <- H2; simpl.
    destruct (connected s pl1) eqn: Lc; [ | exact (H1 pl)].
    unfold SendMessages; simpl.
    destruct (PlayerEqb pl pl1) eqn: Lf; simpl; exact (H1 pl).
Qed.

(* Forward to MovePiece and FixPiece. *)
Lemma FallStepNoSelfMessage : ∀ [s s' pl1 holes Hhole bagNew Hbag]
  (H1 : NoSelfMessage s)
  (H2 : FallStep pl1 holes Hhole bagNew Hbag s = Some s'),
  NoSelfMessage s'.
Proof.
  intros; unfold FallStep in H2.
  destruct (! WinnerMulti s pl1) in H2.
  - destruct (MovePiece pl1 (-1, 0)%Z s) eqn: L1.
    + rewrite H2 in L1.
      exact (MovePieceNoSelfMessage H1 L1).
    + exact (FixPieceNoSelfMessage H1 H2).
  - discriminate H2.
Qed.

(* NewPieceYXState/UnchangedT7Part doesn't touch messages at all. *)
Lemma NewPieceYXStateNoSelfMessage : ∀ [s pyxNew pl1]
  (H1 : NoSelfMessage s),
  NoSelfMessage (NewPieceYXState pyxNew pl1 s).
Proof. intros; exact H1. Qed.

Lemma DropPieceNoSelfMessage : ∀ [s s' pl1 holes Hhole bagNew Hbag]
  (H1 : NoSelfMessage s)
  (H2 : DropPiece pl1 holes Hhole bagNew Hbag s = Some s'),
  NoSelfMessage s'.
Proof.
  intros; unfold DropPiece in H2.
  exact (FixPieceNoSelfMessage (NewPieceYXStateNoSelfMessage H1) H2).
Qed.

(* ReceiveMessage: a self-delivery (msgFrom = pl) would require
messages s pl pl to be both [] (NoSelfMessage s) and a real popped m :: ms
(the match on messages s msgFrom pl) — contradiction, so the append guard
is unreachable for a (pl0, pl0) query either way. *)
Lemma ReceiveMessageNoSelfMessage : ∀ [s s' pl msgFrom]
  (H1 : NoSelfMessage s)
  (H2 : ReceiveMessage pl msgFrom s = Some s'),
  NoSelfMessage s'.
Proof.
  intros; unfold ReceiveMessage in H2.
  destruct (connected s pl) eqn: L1; [ | discriminate H2].
  destruct (messages s msgFrom pl) as [|m ms] eqn: L2; [discriminate H2 |].
  destruct m; inject H2;
    (intro pl0; rewrite <- H2; simpl;
     destruct (PlayerEqb pl0 msgFrom && PlayerEqb pl0 pl) eqn: Lc;
     [ apply andb_true_iff in Lc as [Lc1 Lc2];
       apply PlayerEqbEq1 in Lc1, Lc2;
       assert (Heq : msgFrom = pl) by (transitivity pl0; [symmetry; exact Lc1 | exact Lc2]);
       exfalso; rewrite Heq, (H1 pl) in L2; discriminate L2
     | exact (H1 pl0) ]).
Qed.

(* DisconnectPlayer's own guard checks both (from =? pl1) and !(to =? pl1);
for a (pl, pl) query these are the same boolean, so `b && !b` is always
false (the append never fires on a self-pair). *)
Lemma DisconnectPlayerNoSelfMessage : ∀ [s s' pl1]
  (H1 : NoSelfMessage s)
  (H2 : DisconnectPlayer pl1 s = Some s'),
  NoSelfMessage s'.
Proof.
  intros; unfold DisconnectPlayer in H2.
  destruct (connected s pl1) eqn: L1; [ inject H2 | discriminate H2].
  intro pl; rewrite <- H2; simpl.
  destruct (PlayerEqb pl pl1); rewrite andb_false_r; exact (H1 pl).
Qed.

(* NoticeDisconnection: messages entirely untouched. *)
Lemma NoticeDisconnectionNoSelfMessage : ∀ [s s' pl1]
  (H1 : NoSelfMessage s)
  (H2 : NoticeDisconnection pl1 s = Some s'),
  NoSelfMessage s'.
Proof.
  intros; unfold NoticeDisconnection in H2.
  destruct (! connected s pl1 && connectedView s pl1 pl1); [ inject H2 | discriminate H2].
  intro pl; rewrite <- H2; exact (H1 pl).
Qed.

Lemma StutterNoSelfMessage : ∀ [s s']
  (H1 : NoSelfMessage s)
  (H2 : Some s = Some s'),
  NoSelfMessage s'.
Proof. intros; inject H2; intro pl; rewrite <- H2; exact (H1 pl). Qed.

Lemma NextNoSelfMessage : ∀ [pl e s s']
  (H1 : NoSelfMessage s)
  (H2 : Next pl e s = Some s'),
  NoSelfMessage s'.
Proof.
  intros.
  destruct e in H2; simpl in H2; (
    eapp MovePieceNoSelfMessage || eapp RotatePieceNoSelfMessage ||
    eapp FixPieceNoSelfMessage || eapp FallStepNoSelfMessage ||
    eapp HoldPieceNoSelfMessage || eapp DropPieceNoSelfMessage ||
    eapp RotateKickPieceNoSelfMessage || eapp ReceiveMessageNoSelfMessage ||
    eapp DisconnectPlayerNoSelfMessage || eapp NoticeDisconnectionNoSelfMessage ||
    eapp StutterNoSelfMessage).
Qed.

Theorem SpecNoSelfMessage :
   (∀ bags H, NoSelfMessage (Init bags H))
 ∧ (∀ [pl e s s']
      (H1 : NoSelfMessage s)
      (H2 : Next pl e s = Some s'),
      NoSelfMessage s').
Proof. split; (exact InitNoSelfMessage || exact NextNoSelfMessage). Qed.


(* ========================================================================= *)
(* LastMessagesGameoverDisconnect                                            *)
(* ========================================================================= *)

(* Combining a fresh (0-or-1 garbage, 0-or-1 gameover) suffix with an
already-decomposed garbage-only queue: used by FixPiece, the only op that
ever appends anything past a plain garbage run. *)
Lemma ExtendGarbageThenGameover : ∀ ns (og : option ℕ) (b : bool),
  map GarbageMessage ns ++ (match og with Some n => [GarbageMessage n] | None => [] end)
    ++ (if b then [GameoverMessage] else [])
  = map GarbageMessage (ns ++ match og with Some n => [n] | None => [] end)
      ++ (if b then [GameoverMessage] else []) ++ [].
Proof.
  intros; rewrite app_nil_r, map_app, app_assoc.
  destruct og; reflexivity.
Qed.

(* Init: all queues start empty. *)
Lemma InitLastMessagesGameoverDisconnect : ∀ bags H,
  LastMessagesGameoverDisconnect (Init bags H).
Proof. intros bags H from to Hne; exists [], false, false; reflexivity. Qed.

(* Move/Rotate/Hold/RotateKick (via UpdatePlayer): messages untouched. *)
Lemma GuardedUpdateLastMessagesGameoverDisconnect : ∀ [A s s' pl1] [f : A → option T6.State] [x : A]
  (H1 : LastMessagesGameoverDisconnect s)
  (H2 : (if ! WinnerMulti s pl1 then option_map (UpdatePlayer s pl1) (f x) else None) = Some s'),
  LastMessagesGameoverDisconnect s'.
Proof.
  intros.
  apply IfSome, T5P.OptionMapSome in H2.
  destruct H2 as [s6' [_ E2]].
  intros from to Hne; rewrite <- E2; exact (H1 from to Hne).
Qed.

Lemma MovePieceLastMessagesGameoverDisconnect : ∀ [s s' pl1 dyx]
  (H1 : LastMessagesGameoverDisconnect s)
  (H2 : MovePiece pl1 dyx s = Some s'),
  LastMessagesGameoverDisconnect s'.
Proof. intros; exact (GuardedUpdateLastMessagesGameoverDisconnect H1 H2). Qed.

Lemma RotatePieceLastMessagesGameoverDisconnect : ∀ [s s' pl1 dyx]
  (H1 : LastMessagesGameoverDisconnect s)
  (H2 : RotatePiece pl1 dyx s = Some s'),
  LastMessagesGameoverDisconnect s'.
Proof. intros; exact (GuardedUpdateLastMessagesGameoverDisconnect H1 H2). Qed.

Lemma HoldPieceLastMessagesGameoverDisconnect : ∀ [s s' pl1 holes Hhole bagNew Hbag]
  (H1 : LastMessagesGameoverDisconnect s)
  (H2 : HoldPiece pl1 holes Hhole bagNew Hbag s = Some s'),
  LastMessagesGameoverDisconnect s'.
Proof. intros; exact (GuardedUpdateLastMessagesGameoverDisconnect H1 H2). Qed.

Lemma RotateKickPieceLastMessagesGameoverDisconnect : ∀ [s s' pl1 cw]
  (H1 : LastMessagesGameoverDisconnect s)
  (H2 : RotateKickPiece pl1 cw s = Some s'),
  LastMessagesGameoverDisconnect s'.
Proof. intros; exact (GuardedUpdateLastMessagesGameoverDisconnect H1 H2). Qed.

(* FixPiece: single-player branch is UpdatePlayer again (messages untouched).
Multiplayer: MessageSound(s) rules out an existing GameoverMessage (FixPiece's
own precondition gives gameover s pl1 = false) and an existing DisconnectMessage
(we're in the connected s pl1 = true sub-branch) in the queue about to be
extended. What's left decomposes as plain garbage, onto which the fresh
0-or-1 garbage / 0-or-1 gameover suffix reassembles cleanly. *)
Lemma FixPieceLastMessagesGameoverDisconnect : ∀ [s s' pl1 holes Hhole bagNew Hbag]
  (H1 : LastMessagesGameoverDisconnect s)
  (H2 : MessageSound s)
  (H3 : FixPiece pl1 holes Hhole bagNew Hbag s = Some s'),
  LastMessagesGameoverDisconnect s'.
Proof.
  intros.
  assert (H3' := H3); unfold FixPiece in H3'.
  destruct (! WinnerMulti s pl1) eqn: L1; [ | discriminate H3'].
  destruct (T6.FixPiece bagNew Hbag (s6 s pl1)) as [s6' |] eqn: L2; [ | discriminate H3'].
  unfold option_map in H3'; inject H3'.
  destruct ((PlayerCount =? 1)%nat) eqn: L3.
  - intros from to Hne; rewrite <- H3'; exact (H1 from to Hne).
  - set (gameover' := FP.Gameover' s pl1 s6' holes) in *.
    set (remGenGarbage := FP.RemGenGarbage s pl1 s6') in *.
    assert (Hmsg : ∀ from to, messages s' from to =
        if connected s pl1 && PlayerEqb from pl1 && ! PlayerEqb to pl1
        then messages s from to
               ++ (if PlayerEqb to (target s pl1) && (0 <? remGenGarbage)%nat
                   then [GarbageMessage remGenGarbage] else [])
               ++ (if gameover' then [GameoverMessage] else [])
        else messages s from to). {
      intros from to; rewrite <- H3'; unfold SendMessages; simpl.
      destruct (connected s pl1) eqn: Lc; [ | reflexivity].
      destruct (PlayerEqb from pl1) eqn: Lf; [ | reflexivity].
      destruct (PlayerEqb to pl1) eqn: Lt; reflexivity.
    }
    intros from to Hne; rewrite (Hmsg from to).
    destruct (connected s pl1 && PlayerEqb from pl1 && ! PlayerEqb to pl1) eqn: Lg;
      [ | exact (H1 from to Hne) ].
    apply andb_true_iff in Lg as [Lg1 _]; apply andb_true_iff in Lg1 as [Lc Lf].
    apply PlayerEqbEq1 in Lf; subst from.
    destruct (H1 pl1 to Hne) as [ns [b1 [b2 Heq]]].
    assert (Hb1 : b1 = false). {
      destruct b1; [ | reflexivity]; exfalso.
      assert (Hin : In GameoverMessage (messages s pl1 to)). {
        rewrite Heq; apply in_or_app; right; apply in_or_app; left; left; reflexivity.
      }
      pose proof (proj1 (H2 pl1 to) Hin) as Hgo.
      unfold gameover, T6.gameover in Hgo.
      rewrite (T5P.FixPieceNotGameover L2) in Hgo.
      discriminate Hgo.
    }
    subst b1; simpl in Heq.
    assert (Hb2 : b2 = false). {
      destruct b2; [ | reflexivity]; exfalso.
      assert (Hin : In DisconnectMessage (messages s pl1 to)). {
        rewrite Heq; apply in_or_app; right; left; reflexivity.
      }
      pose proof (proj2 (H2 pl1 to) Hin) as Hdc.
      rewrite Lc in Hdc; discriminate Hdc.
    }
    subst b2; simpl in Heq; rewrite app_nil_r in Heq.
    destruct (PlayerEqb to (target s pl1) && (0 <? remGenGarbage)%nat) eqn: Lgar.
    + destruct gameover' eqn: Hg.
      * exists (ns ++ [remGenGarbage]), true, false.
        rewrite Heq; exact (ExtendGarbageThenGameover ns (Some remGenGarbage) true).
      * exists (ns ++ [remGenGarbage]), false, false.
        rewrite Heq; exact (ExtendGarbageThenGameover ns (Some remGenGarbage) false).
    + destruct gameover' eqn: Hg.
      * exists ns, true, false.
        rewrite Heq; reflexivity.
      * exists ns, false, false.
        rewrite Heq; reflexivity.
Qed.

(* Forward to MovePiece and FixPiece. *)
Lemma FallStepLastMessagesGameoverDisconnect : ∀ [s s' pl1 holes Hhole bagNew Hbag]
  (H1 : LastMessagesGameoverDisconnect s)
  (H2 : MessageSound s)
  (H3 : FallStep pl1 holes Hhole bagNew Hbag s = Some s'),
  LastMessagesGameoverDisconnect s'.
Proof.
  intros; unfold FallStep in H3.
  destruct (! WinnerMulti s pl1) in H3.
  - destruct (MovePiece pl1 (-1, 0)%Z s) eqn: L1.
    + rewrite H3 in L1.
      exact (MovePieceLastMessagesGameoverDisconnect H1 L1).
    + exact (FixPieceLastMessagesGameoverDisconnect H1 H2 H3).
  - discriminate H3.
Qed.

(* NewPieceYXState/UnchangedT7Part doesn't touch messages at all. *)
Lemma NewPieceYXStateLastMessagesGameoverDisconnect : ∀ [s pyxNew pl1]
  (Hd : LastMessagesGameoverDisconnect s),
  LastMessagesGameoverDisconnect (NewPieceYXState pyxNew pl1 s).
Proof. intros; now apply Hd. Qed.

Lemma NewPieceYXStateMessagesUnchanged : ∀ s pyxNew pl1,
  messages (NewPieceYXState pyxNew pl1 s) = messages s.
Proof. reflexivity. Qed.

Lemma DropPieceLastMessagesGameoverDisconnect : ∀ [s s' pl1 holes Hhole bagNew Hbag]
  (H1 : LastMessagesGameoverDisconnect s)
  (H2 : MessageSound s)
  (H3 : DropPiece pl1 holes Hhole bagNew Hbag s = Some s'),
  LastMessagesGameoverDisconnect s'.
Proof.
  intros; unfold DropPiece in H3.
  set (sNew := NewPieceYXState (gy s pl1, px s pl1) pl1 s).
  assert (L1 : LastMessagesGameoverDisconnect sNew). {
    exact (NewPieceYXStateLastMessagesGameoverDisconnect H1).
  }
  assert (L2 : MessageSound sNew). {
    unfold MessageSound, sNew; intros.
    pose proof (@NewPieceYXStateGameoverUnchanged s (gy s pl1, px s pl1) pl1 from) as L2_1.
    pose proof (@NewPieceYXStateConnectedUnchanged s (gy s pl1, px s pl1) pl1) as L2_2.
    pose proof (@NewPieceYXStateMessagesUnchanged s (gy s pl1, px s pl1) pl1) as L2_3.
    rewrite L2_1, L2_2, L2_3; exact (H2 from to).
  }
  exact (FixPieceLastMessagesGameoverDisconnect L1 L2 H3).
Qed.

(* ReceiveMessage only ever pops a queue's head. A self-delivery (msgFrom = pl)
is impossible given NoSelfMessage(s) (the popped queue would have to be both
[] and a real m :: ms). Otherwise, popping the head of an already-decomposed
queue keeps the same shape: strip the first garbage entry if there was one
(ns = n :: ns'), or otherwise strip the GameoverMessage or the sole
DisconnectMessage. *)
Lemma ReceiveMessageLastMessagesGameoverDisconnect : ∀ [s s' pl msgFrom]
  (H1 : LastMessagesGameoverDisconnect s)
  (H2 : NoSelfMessage s)
  (H3 : ReceiveMessage pl msgFrom s = Some s'),
  LastMessagesGameoverDisconnect s'.
Proof.
  intros; unfold ReceiveMessage in H3.
  destruct (connected s pl) eqn: L1; [ | discriminate H3].
  destruct (messages s msgFrom pl) as [|m ms] eqn: L2; [discriminate H3 |].
  assert (Hne0 : msgFrom ≠ pl). {
    intro Heq0; subst msgFrom.
    rewrite (H2 pl) in L2; discriminate L2.
  }
  assert (Hmsg : ∀ from to, messages s' from to =
      if PlayerEqb from msgFrom && PlayerEqb to pl then ms else messages s from to)
    by (intros; destruct m; inject H3; now rewrite <- H3).
  intros from to Hne; rewrite (Hmsg from to).
  destruct (PlayerEqb from msgFrom && PlayerEqb to pl) eqn: Lc;
    [ | exact (H1 from to Hne) ].
  apply andb_true_iff in Lc as [Lf Lt]; apply PlayerEqbEq1 in Lf, Lt; subst from to.
  destruct (H1 msgFrom pl Hne0) as [ns [b1 [b2 Heq]]].
  rewrite L2 in Heq.
  destruct ns as [| n ns'].
  - simpl in Heq.
    destruct b1 eqn: Hb1; simpl in Heq.
    + injection Heq as _ Heqms.
      exists [], false, b2.
      simpl; exact Heqms.
    + destruct b2 eqn: Hb2; simpl in Heq.
      * injection Heq as _ Heqms.
        exists [], false, false.
        simpl; exact Heqms.
      * discriminate Heq.
  - simpl in Heq.
    injection Heq as _ Heqms.
    exists ns', b1, b2.
    exact Heqms.
Qed.

(* DisconnectPlayer is the only op that ever appends a DisconnectMessage.
MessageSound(s) rules out an existing one (we're in the connected s pl1 = true
branch); a GameoverMessage may already be there (that's fine, the shape
allows GameoverMessage then DisconnectMessage). *)
Lemma DisconnectPlayerLastMessagesGameoverDisconnect : ∀ [s s' pl1]
  (H1 : LastMessagesGameoverDisconnect s)
  (H2 : MessageSound s)
  (H3 : DisconnectPlayer pl1 s = Some s'),
  LastMessagesGameoverDisconnect s'.
Proof.
  intros; unfold DisconnectPlayer in H3.
  destruct (connected s pl1) eqn: L1; [ inject H3 | discriminate H3].
  assert (Hmsg : ∀ from to, messages s' from to =
      if ! PlayerEqb pl1 Host && PlayerEqb from pl1 && ! PlayerEqb to pl1
      then messages s from to ++ [DisconnectMessage] else messages s from to)
    by (intros; now rewrite <- H3).
  intros from to Hne; rewrite (Hmsg from to).
  destruct (! PlayerEqb pl1 Host && PlayerEqb from pl1 && ! PlayerEqb to pl1) eqn: Lg;
    [ | exact (H1 from to Hne) ].
  apply andb_true_iff in Lg as [Lg1 _]; apply andb_true_iff in Lg1 as [_ Lf].
  apply PlayerEqbEq1 in Lf; subst from.
  destruct (H1 pl1 to Hne) as [ns [b1 [b2 Heq]]].
  assert (Hb2 : b2 = false). {
    destruct b2; [ | reflexivity]; exfalso.
    assert (Hin : In DisconnectMessage (messages s pl1 to)). {
      rewrite Heq; apply in_or_app; right.
      destruct b1; simpl; [right; left; reflexivity | left; reflexivity].
    }
    pose proof (proj2 (H2 pl1 to) Hin) as Hdc.
    rewrite L1 in Hdc; discriminate Hdc.
  }
  subst b2; simpl in Heq; rewrite app_nil_r in Heq.
  exists ns, b1, true.
  rewrite Heq, app_assoc; reflexivity.
Qed.

(* NoticeDisconnection: messages entirely untouched. *)
Lemma NoticeDisconnectionLastMessagesGameoverDisconnect : ∀ [s s' pl1]
  (H1 : LastMessagesGameoverDisconnect s)
  (H2 : NoticeDisconnection pl1 s = Some s'),
  LastMessagesGameoverDisconnect s'.
Proof.
  intros; unfold NoticeDisconnection in H2.
  destruct (! connected s pl1 && connectedView s pl1 pl1); [ inject H2 | discriminate H2].
  intros from to Hne; rewrite <- H2; exact (H1 from to Hne).
Qed.

Lemma StutterLastMessagesGameoverDisconnect : ∀ [s s']
  (H1 : LastMessagesGameoverDisconnect s)
  (H2 : Some s = Some s'),
  LastMessagesGameoverDisconnect s'.
Proof. intros; inject H2; intros from to Hne; rewrite <- H2; exact (H1 from to Hne). Qed.

Lemma NextLastMessagesGameoverDisconnect : ∀ [pl e s s']
  (H1 : LastMessagesGameoverDisconnect s)
  (H2 : MessageSound s)
  (H3 : NoSelfMessage s)
  (H4 : Next pl e s = Some s'),
  LastMessagesGameoverDisconnect s'.
Proof.
  intros.
  destruct e in H4; simpl in H4; (
    eapp MovePieceLastMessagesGameoverDisconnect || eapp RotatePieceLastMessagesGameoverDisconnect ||
    eapp FixPieceLastMessagesGameoverDisconnect || eapp FallStepLastMessagesGameoverDisconnect ||
    eapp HoldPieceLastMessagesGameoverDisconnect || eapp DropPieceLastMessagesGameoverDisconnect ||
    eapp RotateKickPieceLastMessagesGameoverDisconnect ||
    eapp ReceiveMessageLastMessagesGameoverDisconnect ||
    eapp DisconnectPlayerLastMessagesGameoverDisconnect ||
    eapp NoticeDisconnectionLastMessagesGameoverDisconnect ||
    eapp StutterLastMessagesGameoverDisconnect).
Qed.

Theorem SpecLastMessagesGameoverDisconnect :
   (∀ bags H, LastMessagesGameoverDisconnect (Init bags H))
 ∧ (∀ [pl e s s']
      (H1 : LastMessagesGameoverDisconnect s)
      (H2 : MessageSound s)
      (H3 : NoSelfMessage s)
      (H4 : Next pl e s = Some s'),
      LastMessagesGameoverDisconnect s').
Proof. split; (exact InitLastMessagesGameoverDisconnect || exact NextLastMessagesGameoverDisconnect). Qed.


(* ========================================================================= *)
(* TargetNotSelf                                                             *)
(* ========================================================================= *)

Section Player.
Open Scope player_scope.

(* Nat.iter's own recursion unfolds the OTHER way (Nat.iter (S n) f x =
f (Nat.iter n f x), applying f last) — this is the direction actually needed,
proved directly rather than assumed. *)
Lemma IterSuccR : ∀ (f : Player → Player) n x, (f ** (S n)) x = (f ** n) (f x).
Proof.
  intros f n; induction n as [| n' H1]; intro x.
  - reflexivity.
  - simpl; rewrite <- (H1 x); reflexivity.
Qed.

(* If NextTargetAux exhausts its fuel and returns self, none of the fuel
candidates it checked (the first `fuel` iterates of PlayerNext from pl)
satisfied `playing ∧ ≠ self`. *)
Lemma NextTargetAuxSelfMeansNonePlaying : ∀ fuel playing self pl,
  NextTargetAux fuel playing self pl = self →
  ∀ k, k < fuel →
    playing ((PlayerNext ** (S k)) pl) = false ∨ (PlayerNext ** (S k)) pl = self.
Proof.
  induction fuel as [| fuel' H1]; intros playing self pl H2 k H3.
  - lia.
  - simpl in H2.
    destruct (playing (PlayerNext pl) && ! PlayerEqb (PlayerNext pl) self) eqn: H4.
    + apply andb_true_iff in H4 as [_ H5]; apply negb_true_iff in H5.
      apply PlayerEqbEq3 in H5; exfalso; exact (H5 H2).
    + destruct k as [| k'].
      * apply andb_false_iff in H4 as [H5 | H5].
        -- left; simpl; exact H5.
        -- apply negb_false_iff in H5; apply PlayerEqbEq1 in H5.
           right; simpl; exact H5.
      * assert (H5 : k' < fuel') by lia.
        destruct (H1 playing self (PlayerNext pl) H2 k' H5) as [H6 | H6].
        -- left; rewrite (IterSuccR PlayerNext (S k') pl); exact H6.
        -- right; rewrite (IterSuccR PlayerNext (S k') pl); exact H6.
Qed.

Lemma NextTargetAuxNotSelf : ∀ fuel playing self pl pl2 k,
  k < fuel →
  (PlayerNext ** (S k)) pl = pl2 →
  playing pl2 = true →
  pl2 ≠ self →
  NextTargetAux fuel playing self pl ≠ self.
Proof.
  intros fuel playing self pl pl2 k H1 H2 H3 H4 H5.
  destruct (NextTargetAuxSelfMeansNonePlaying fuel playing self pl H5 k H1) as [H6 | H6].
  - rewrite H2 in H6; rewrite H6 in H3; discriminate H3.
  - exact (H4 (eq_trans (eq_sym H2) H6)).
Qed.

(* Whichever candidate NextTargetAux actually returns (other than self, via
its fuel-exhausted fallback), it was returned specifically because the guard
`playing pl2 && !(pl2 =? self)` fired on it (a fact read directly off the
fixpoint's own shape, with no need for the cyclic-permutation search-
termination argument NextTargetAuxNotSelf needed for the opposite fact). *)
Lemma NextTargetAuxPlayingWhenNotSelf : ∀ fuel playing self pl,
  NextTargetAux fuel playing self pl ≠ self →
  playing (NextTargetAux fuel playing self pl) = true.
Proof.
  induction fuel as [| fuel' IH]; intros playing self pl H1.
  - simpl in H1; exfalso; exact (H1 eq_refl).
  - simpl in H1 |- *.
    destruct (playing (PlayerNext pl) && ! PlayerEqb (PlayerNext pl) self) eqn: H2.
    + apply andb_true_iff in H2 as [H2a H2b]; exact H2a.
    + exact (IH playing self (PlayerNext pl) H1).
Qed.

End Player.

(* Init: PlayerNext pl ≠ pl follows from PlayerCyclicPermutation's uniqueness
applied to pl itself (n = 0 and n = 1 both reaching pl would violate it). *)
Lemma InitTargetNotSelf : ∀ bags H,
  PlayerCount > 1 → NoWinner (Init bags H) → ∀ pl, target (Init bags H) pl ≠ pl.
Proof.
  intros bags H H1 H2 pl H3.
  simpl in H3.
  destruct (PlayerCyclicPermutation pl pl) as [n [[H4 H5] H6]].
  assert (H7 : n = 0) by (apply H6; split; [lia | reflexivity]).
  assert (H8 : n = 1) by (apply H6; split; [lia | simpl; exact H3]).
  rewrite H7 in H8; discriminate H8.
Qed.

(* A really-playing player at s' was already really-playing at s, given
gameover/connected only ever move the "wrong" way (GameoverMonotone /
DisconnectedMonotone, used contrapositively). *)
Lemma PlayingBackward : ∀ [s s' pl2]
  (H1 : gameover s pl2 = true → gameover s' pl2 = true)
  (H2 : connected s pl2 = false → connected s' pl2 = false)
  (H3 : Playing s' pl2 = true),
  Playing s pl2 = true.
Proof.
  intros; unfold Playing in *.
  apply andb_true_iff in H3 as [H4 H5]; apply andb_true_iff.
  split.
  - apply negb_true_iff; apply negb_true_iff in H4.
    destruct (gameover s pl2) eqn: H6; [ | reflexivity].
    rewrite (H1 eq_refl) in H4; discriminate H4.
  - destruct (connected s pl2) eqn: H6; [reflexivity |].
    rewrite (H2 eq_refl) in H5; discriminate H5.
Qed.

Lemma NoWinnerBackward : ∀ [s s']
  (H1 : ∀ pl2, gameover s pl2 = true → gameover s' pl2 = true)
  (H2 : ∀ pl2, connected s pl2 = false → connected s' pl2 = false)
  (H3 : NoWinner s'),
  NoWinner s.
Proof.
  intros.
  destruct H3 as [q1 [q2 [H4 [H5 H6]]]].
  exists q1, q2.
  split; [exact H4 | split].
  - exact (PlayingBackward (H1 q1) (H2 q1) H5).
  - exact (PlayingBackward (H1 q2) (H2 q2) H6).
Qed.

(* Move/Rotate/Hold/RotateKick (via UpdatePlayer): target untouched, and
NoWinner s' -> NoWinner s via the already-proven Monotone lemmas. *)
Lemma GuardedUpdateTargetNotSelf : ∀ [A s s' pl1] [f : A → option T6.State] [x : A]
  (H1 : (if ! WinnerMulti s pl1 then option_map (UpdatePlayer s pl1) (f x) else None) = Some s'),
  ∀ pl2, target s' pl2 = target s pl2.
Proof.
  intros.
  apply IfSome, T5P.OptionMapSome in H1.
  destruct H1 as [s6' [_ H2]].
  rewrite <- H2; reflexivity.
Qed.

Lemma MovePieceTargetNotSelf : ∀ [s s' pl1 dyx]
  (H1 : PlayerCount > 1 → NoWinner s → ∀ pl, target s pl ≠ pl)
  (H2 : MovePiece pl1 dyx s = Some s')
  (H3 : PlayerCount > 1) (H4 : NoWinner s'), ∀ pl, target s' pl ≠ pl.
Proof.
  intros.
  rewrite (GuardedUpdateTargetNotSelf H2).
  apply H1; [exact H3 |].
  exact (NoWinnerBackward (λ pl2, MovePieceGameoverMonotone H2) (λ pl2, MovePieceConnectedMonotone H2) H4).
Qed.

Lemma RotatePieceTargetNotSelf : ∀ [s s' pl1 dyx]
  (H1 : PlayerCount > 1 → NoWinner s → ∀ pl, target s pl ≠ pl)
  (H2 : RotatePiece pl1 dyx s = Some s')
  (H3 : PlayerCount > 1) (H4 : NoWinner s'), ∀ pl, target s' pl ≠ pl.
Proof.
  intros.
  rewrite (GuardedUpdateTargetNotSelf H2).
  apply H1; [exact H3 |].
  exact (NoWinnerBackward (λ pl2, RotatePieceGameoverMonotone H2) (λ pl2, RotatePieceConnectedMonotone H2) H4).
Qed.

Lemma HoldPieceTargetNotSelf : ∀ [s s' pl1 holes H1' bagNew H2']
  (H1 : PlayerCount > 1 → NoWinner s → ∀ pl, target s pl ≠ pl)
  (H2 : HoldPiece pl1 holes H1' bagNew H2' s = Some s')
  (H3 : PlayerCount > 1) (H4 : NoWinner s'), ∀ pl, target s' pl ≠ pl.
Proof.
  intros.
  rewrite (GuardedUpdateTargetNotSelf H2).
  apply H1; [exact H3 |].
  exact (NoWinnerBackward (λ pl2, HoldPieceGameoverMonotone H2) (λ pl2, HoldPieceConnectedMonotone H2) H4).
Qed.

Lemma RotateKickPieceTargetNotSelf : ∀ [s s' pl1 cw]
  (H1 : PlayerCount > 1 → NoWinner s → ∀ pl, target s pl ≠ pl)
  (H2 : RotateKickPiece pl1 cw s = Some s')
  (H3 : PlayerCount > 1) (H4 : NoWinner s'), ∀ pl, target s' pl ≠ pl.
Proof.
  intros.
  rewrite (GuardedUpdateTargetNotSelf H2).
  apply H1; [exact H3 |].
  exact (NoWinnerBackward (λ pl2, RotateKickPieceGameoverMonotone H2)
    (λ pl2, RotateKickPieceConnectedMonotone H2) H4).
Qed.

(* FixPiece: single-player branch is vacuous (PlayerCount = 1 contradicts the
invariant's own PlayerCount > 1 hypothesis). Multiplayer: only pl1's own
target can move, and only when she has garbage to send and isn't herself
gameover. NoWinner s' gives two really-playing players; at least one, pl2', is
<> pl1; ViewSound(s) lifts "really playing" to "pl1's own view says playing"
for pl2' (FixPiece never touches pl1's view of anyone but herself); and
PlayerCyclicPermutation, anchored at PlayerNext (target s pl1) (the loop's
first checked candidate), places pl2' within PlayerCount steps (so
NextTargetAuxNotSelf applies). *)
Section Player.
Open Scope player_scope.

Lemma FixPieceTargetNotSelf : ∀ [s s' pl1 holes H1' bagNew H2']
  (H1 : PlayerCount > 1 → NoWinner s → ∀ pl, target s pl ≠ pl)
  (H2 : ViewSound s)
  (H3 : FixPiece pl1 holes H1' bagNew H2' s = Some s')
  (H4 : PlayerCount > 1) (H5 : NoWinner s'), ∀ pl, target s' pl ≠ pl.
Proof.
  intros.
  assert (H6 : NoWinner s)
    by exact (NoWinnerBackward (λ pl2, FixPieceGameoverMonotone H3) (λ pl2, FixPieceConnectedMonotone H3) H5).
  assert (H3' := H3); unfold FixPiece in H3'.
  destruct (! WinnerMulti s pl1) eqn: H7; [ | discriminate H3'].
  destruct (T6.FixPiece bagNew H2' (s6 s pl1)) as [s6' |] eqn: H8; [ | discriminate H3'].
  unfold option_map in H3'; inject H3'.
  destruct ((PlayerCount =? 1)%nat) eqn: H9.
  - apply Nat.eqb_eq in H9; lia.
  - set (gameover' := FP.Gameover' s pl1 s6' holes) in *.
    set (remGenGarbage := FP.RemGenGarbage s pl1 s6') in *.
    assert (H10 : ∀ pl2, target s' pl2 =
        if PlayerEqb pl2 pl1 && (0 <? remGenGarbage)%nat && ! gameover'
        then NextTarget (FP.PlayingView' s pl1 s6' holes) pl1 (target s pl1)
        else target s pl2)
      by (intros; now rewrite <- H3').
    rewrite (H10 pl).
    destruct (PlayerEqb pl pl1 && (0 <? remGenGarbage)%nat && ! gameover') eqn: H11;
      [ | exact (H1 H4 H6 pl) ].
    intro H12.
    assert (H13 : ∃ pl2', pl2' ≠ pl1 ∧ Playing s' pl2' = true). {
      destruct H5 as [q1 [q2 [H14 [H15 H16]]]].
      destruct (PlayerEqb q1 pl1) eqn: H17.
      - apply PlayerEqbEq1 in H17; subst q1.
        exists q2; split; [ | exact H16].
        intro H18; apply H14; exact (eq_sym H18).
      - apply PlayerEqbEq3 in H17.
        exists q1; split; [exact H17 | exact H15].
    }
    destruct H13 as [pl2' [H14 H15]].
    assert (H16 : Playing s pl2' = true)
      by exact (PlayingBackward (FixPieceGameoverMonotone H3) (FixPieceConnectedMonotone H3) H15).
    assert (H17 : PlayingView s pl1 pl2' = true). {
      unfold PlayingView, Playing in *.
      apply andb_true_iff in H16 as [H18 H19]; apply negb_true_iff in H18.
      apply andb_true_iff; split.
      - apply negb_true_iff.
        destruct (gameoverView s pl1 pl2') eqn: H20; [ | reflexivity].
        exfalso.
        pose proof (proj1 (H2 pl1 pl2') H20) as H21.
        rewrite H21 in H18; discriminate H18.
      - destruct (connectedView s pl1 pl2') eqn: H20; [reflexivity |].
        exfalso.
        pose proof (proj2 (H2 pl1 pl2') H20) as H21.
        rewrite H21 in H19; discriminate H19.
    }
    assert (H18 : FP.PlayingView' s pl1 s6' holes pl2' = true). {
      unfold FP.PlayingView', FP.GameoverView'.
      destruct (PlayerEqb pl2' pl1) eqn: H19.
      - apply PlayerEqbEq1 in H19; exfalso; exact (H14 H19).
      - unfold PlayingView in H17; exact H17.
    }
    destruct (PlayerCyclicPermutation (PlayerNext (target s pl1)) pl2') as [n [[H19 H20] H21]].
    assert (H22 : (PlayerNext ** (S n)) (target s pl1) = pl2')
      by (rewrite (IterSuccR PlayerNext n (target s pl1)); exact H20).
    unfold NextTarget in H12.
    (* H11 only tells us the redirect fired for a player equal to pl1 up to
    PlayerEqb; NextTargetAuxNotSelf's conclusion is stated against `self` =
    pl1, so pl must first be identified with pl1 before H12 can feed it. *)
    apply andb_true_iff in H11 as [H11a H11b].
    apply andb_true_iff in H11a as [H11c H11d].
    apply PlayerEqbEq1 in H11c; subst pl.
    exact (NextTargetAuxNotSelf PlayerCount (FP.PlayingView' s pl1 s6' holes) pl1
             (target s pl1) pl2' n H19 H22 H18 H14 H12).
Qed.

End Player.

(* Forward to MovePiece and FixPiece. *)
Lemma FallStepTargetNotSelf : ∀ [s s' pl1 holes H1' bagNew H2']
  (H1 : PlayerCount > 1 → NoWinner s → ∀ pl, target s pl ≠ pl)
  (H2 : ViewSound s)
  (H3 : FallStep pl1 holes H1' bagNew H2' s = Some s')
  (H4 : PlayerCount > 1) (H5 : NoWinner s'), ∀ pl, target s' pl ≠ pl.
Proof.
  intros; unfold FallStep in H3.
  destruct (! WinnerMulti s pl1) in H3.
  - destruct (MovePiece pl1 (-1, 0)%Z s) eqn: H6.
    + rewrite H3 in H6.
      exact (MovePieceTargetNotSelf H1 H6 H4 H5 pl).
    + exact (FixPieceTargetNotSelf H1 H2 H3 H4 H5 pl).
  - discriminate H3.
Qed.

Lemma NewPieceYXStateTargetUnchanged : ∀ s pyxNew pl1,
  target (NewPieceYXState pyxNew pl1 s) = target s.
Proof. reflexivity. Qed.

Lemma NewPieceYXStateTargetNotSelf : ∀ [s pyxNew pl1]
  (H1 : PlayerCount > 1 → NoWinner s → ∀ pl, target s pl ≠ pl)
  (H2 : PlayerCount > 1) (H3 : NoWinner (NewPieceYXState pyxNew pl1 s)),
  ∀ pl, target (NewPieceYXState pyxNew pl1 s) pl ≠ pl.
Proof.
  intros.
  rewrite NewPieceYXStateTargetUnchanged.
  apply H1; [exact H2 |].
  destruct H3 as [q1 [q2 [H4 [H5 H6]]]].
  exists q1, q2; repeat split.
  - exact H4.
  - unfold Playing in *.
    rewrite (NewPieceYXStateGameoverUnchanged q1), (NewPieceYXStateConnectedUnchanged s pyxNew pl1) in H5.
    exact H5.
  - unfold Playing in *.
    rewrite (NewPieceYXStateGameoverUnchanged q2), (NewPieceYXStateConnectedUnchanged s pyxNew pl1) in H6.
    exact H6.
Qed.

Lemma DropPieceTargetNotSelf : ∀ [s s' pl1 holes H1' bagNew H2']
  (H1 : PlayerCount > 1 → NoWinner s → ∀ pl, target s pl ≠ pl)
  (H2 : ViewSound s)
  (H3 : DropPiece pl1 holes H1' bagNew H2' s = Some s')
  (H4 : PlayerCount > 1) (H5 : NoWinner s'), ∀ pl, target s' pl ≠ pl.
Proof.
  intros.
  exact (FixPieceTargetNotSelf (NewPieceYXStateTargetNotSelf H1) (NewPieceYXStateViewSound H2) H3 H4 H5 pl).
Qed.

(* ReceiveMessage: GarbageMessage leaves target untouched. GameoverMessage/
DisconnectMessage may redirect pl1's own target away from the message's
sender pl2, exactly as FixPiece's own redirect does. MessageSound rules pl2
out as a live candidate (her queued Gameover/Disconnect message can only have
been sent once she genuinely was gameover/disconnected), so the same
cyclic-search argument applies, with pl2 playing the role of the walk's
starting point instead of pl1's own prior target. *)
Lemma ReceiveMessageTargetNotSelf : ∀ [s s' pl1 pl2]
  (H1 : PlayerCount > 1 → NoWinner s → ∀ pl, target s pl ≠ pl)
  (H2 : ViewSound s)
  (H3 : MessageSound s)
  (H4 : ReceiveMessage pl1 pl2 s = Some s')
  (H5 : PlayerCount > 1) (H6 : NoWinner s'), ∀ pl, target s' pl ≠ pl.
Proof.
  intros.
  unfold ReceiveMessage in H4.
  destruct (connected s pl1) eqn: H7; [ | discriminate H4].
  destruct (messages s pl2 pl1) as [|m ms] eqn: H8; [discriminate H4 |].
  assert (H9 : ∀ q, gameover s' q = gameover s q)
    by (intro; destruct m; inject H4; unfold gameover; now rewrite <- H4).
  assert (H10 : ∀ q, connected s' q = connected s q)
    by (intro; destruct m; inject H4; now rewrite <- H4).
  assert (H11 : NoWinner s). {
    destruct H6 as [q1 [q2 [H12 [H13 H14]]]].
    exists q1, q2; repeat split.
    - exact H12.
    - unfold Playing in *; rewrite <- (H9 q1), <- (H10 q1); exact H13.
    - unfold Playing in *; rewrite <- (H9 q2), <- (H10 q2); exact H14.
  }
  destruct m eqn: Hm.
  - (* GarbageMessage: target untouched *)
    assert (H12 : target s' = target s) by (inject H4; now rewrite <- H4).
    rewrite H12; exact (H1 H5 H11 pl).
  - (* GameoverMessage: may redirect pl1's own target away from pl2 *)
    inject H4.
    assert (H12 : ∀ pl3, target s' pl3 =
        if PlayerEqb pl3 pl1 && PlayerEqb (target s pl1) pl2 then
          NextTarget (λ pl4, if PlayerEqb pl4 pl2 then false else PlayingView s pl1 pl4) pl1 pl2
        else target s pl3)
      by (intro; now rewrite <- H4).
    rewrite (H12 pl).
    destruct (PlayerEqb pl pl1 && PlayerEqb (target s pl1) pl2) eqn: H13;
      [ | exact (H1 H5 H11 pl) ].
    intro H14.
    apply andb_true_iff in H13 as [H13a H13b].
    apply PlayerEqbEq1 in H13a; subst pl.
    unfold NextTarget in H14.
    assert (H15 : gameover s pl2 = true)
      by (apply (proj1 (H3 pl2 pl1)); rewrite H8; apply in_eq).
    assert (H16 : Playing s pl2 = false)
      by (unfold Playing; rewrite H15; reflexivity).
    assert (H17 : ∃ pl3', pl3' ≠ pl1 ∧ pl3' ≠ pl2 ∧ Playing s pl3' = true). {
      destruct H11 as [q1 [q2 [H18 [H19 H20]]]].
      assert (H21 : q1 ≠ pl2) by (intro Heq; subst q1; rewrite H16 in H19; discriminate H19).
      assert (H22 : q2 ≠ pl2) by (intro Heq; subst q2; rewrite H16 in H20; discriminate H20).
      destruct (PlayerEqb q1 pl1) eqn: H23.
      - apply PlayerEqbEq1 in H23; subst q1.
        exists q2; repeat split; [ | exact H22 | exact H20].
        intro Heq; apply H18; exact (eq_sym Heq).
      - apply PlayerEqbEq3 in H23.
        exists q1; repeat split; [exact H23 | exact H21 | exact H19].
    }
    destruct H17 as [pl3' [H18 [H19 H20]]].
    assert (H21 : PlayingView s pl1 pl3' = true). {
      unfold PlayingView, Playing in *.
      apply andb_true_iff in H20 as [H22 H23]; apply negb_true_iff in H22.
      apply andb_true_iff; split.
      - apply negb_true_iff.
        destruct (gameoverView s pl1 pl3') eqn: H24; [ | reflexivity].
        exfalso; pose proof (proj1 (H2 pl1 pl3') H24) as H25.
        rewrite H25 in H22; discriminate H22.
      - destruct (connectedView s pl1 pl3') eqn: H24; [reflexivity |].
        exfalso; pose proof (proj2 (H2 pl1 pl3') H24) as H25.
        rewrite H25 in H23; discriminate H23.
    }
    assert (H22 : (λ pl4, if PlayerEqb pl4 pl2 then false else PlayingView s pl1 pl4) pl3' = true). {
      simpl; destruct (PlayerEqb pl3' pl2) eqn: H23.
      - apply PlayerEqbEq1 in H23; exfalso; exact (H19 H23).
      - exact H21.
    }
    destruct (PlayerCyclicPermutation (PlayerNext pl2) pl3') as [n [[H23 H24] H25]].
    assert (H26 : (PlayerNext ** (S n)) pl2 = pl3')
      by (rewrite (IterSuccR PlayerNext n pl2); exact H24).
    exact (NextTargetAuxNotSelf PlayerCount
             (λ pl4, if PlayerEqb pl4 pl2 then false else PlayingView s pl1 pl4)
             pl1 pl2 pl3' n H23 H26 H22 H18 H14).
  - (* DisconnectMessage: same argument, via connectedness instead of gameover *)
    inject H4.
    assert (H12 : ∀ pl3, target s' pl3 =
        if PlayerEqb pl3 pl1 && PlayerEqb (target s pl1) pl2 then
          NextTarget (λ pl4, if PlayerEqb pl4 pl2 then false else PlayingView s pl1 pl4) pl1 pl2
        else target s pl3)
      by (intro; now rewrite <- H4).
    rewrite (H12 pl).
    destruct (PlayerEqb pl pl1 && PlayerEqb (target s pl1) pl2) eqn: H13;
      [ | exact (H1 H5 H11 pl) ].
    intro H14.
    apply andb_true_iff in H13 as [H13a H13b].
    apply PlayerEqbEq1 in H13a; subst pl.
    unfold NextTarget in H14.
    assert (H15 : connected s pl2 = false)
      by (apply (proj2 (H3 pl2 pl1)); rewrite H8; apply in_eq).
    assert (H16 : Playing s pl2 = false)
      by (unfold Playing; rewrite H15, andb_false_r; reflexivity).
    assert (H17 : ∃ pl3', pl3' ≠ pl1 ∧ pl3' ≠ pl2 ∧ Playing s pl3' = true). {
      destruct H11 as [q1 [q2 [H18 [H19 H20]]]].
      assert (H21 : q1 ≠ pl2) by (intro Heq; subst q1; rewrite H16 in H19; discriminate H19).
      assert (H22 : q2 ≠ pl2) by (intro Heq; subst q2; rewrite H16 in H20; discriminate H20).
      destruct (PlayerEqb q1 pl1) eqn: H23.
      - apply PlayerEqbEq1 in H23; subst q1.
        exists q2; repeat split; [ | exact H22 | exact H20].
        intro Heq; apply H18; exact (eq_sym Heq).
      - apply PlayerEqbEq3 in H23.
        exists q1; repeat split; [exact H23 | exact H21 | exact H19].
    }
    destruct H17 as [pl3' [H18 [H19 H20]]].
    assert (H21 : PlayingView s pl1 pl3' = true). {
      unfold PlayingView, Playing in *.
      apply andb_true_iff in H20 as [H22 H23]; apply negb_true_iff in H22.
      apply andb_true_iff; split.
      - apply negb_true_iff.
        destruct (gameoverView s pl1 pl3') eqn: H24; [ | reflexivity].
        exfalso; pose proof (proj1 (H2 pl1 pl3') H24) as H25.
        rewrite H25 in H22; discriminate H22.
      - destruct (connectedView s pl1 pl3') eqn: H24; [reflexivity |].
        exfalso; pose proof (proj2 (H2 pl1 pl3') H24) as H25.
        rewrite H25 in H23; discriminate H23.
    }
    assert (H22 : (λ pl4, if PlayerEqb pl4 pl2 then false else PlayingView s pl1 pl4) pl3' = true). {
      simpl; destruct (PlayerEqb pl3' pl2) eqn: H23.
      - apply PlayerEqbEq1 in H23; exfalso; exact (H19 H23).
      - exact H21.
    }
    destruct (PlayerCyclicPermutation (PlayerNext pl2) pl3') as [n [[H23 H24] H25]].
    assert (H26 : (PlayerNext ** (S n)) pl2 = pl3')
      by (rewrite (IterSuccR PlayerNext n pl2); exact H24).
    exact (NextTargetAuxNotSelf PlayerCount
             (λ pl4, if PlayerEqb pl4 pl2 then false else PlayingView s pl1 pl4)
             pl1 pl2 pl3' n H23 H26 H22 H18 H14).
Qed.

(* DisconnectPlayer: target and gameover untouched; connected is monotone
(DisconnectPlayerConnectedMonotone) so NoWinner s' -> NoWinner s still holds. *)
Lemma DisconnectPlayerTargetNotSelf : ∀ [s s' pl1]
  (H1 : PlayerCount > 1 → NoWinner s → ∀ pl, target s pl ≠ pl)
  (H2 : DisconnectPlayer pl1 s = Some s')
  (H3 : PlayerCount > 1) (H4 : NoWinner s'), ∀ pl, target s' pl ≠ pl.
Proof.
  intros.
  assert (H5 := H2); unfold DisconnectPlayer in H5.
  destruct (connected s pl1) eqn: H6; [ inject H5 | discriminate H5].
  assert (H7 : target s' = target s) by now rewrite <- H5.
  assert (H8 : ∀ pl2, gameover s' pl2 = gameover s pl2)
    by (intro; unfold gameover; now rewrite <- H5).
  rewrite H7.
  apply H1; [exact H3 |].
  exact (NoWinnerBackward (λ pl2 H9, eq_trans (H8 pl2) H9)
           (λ pl2, DisconnectPlayerConnectedMonotone H2) H4).
Qed.

(* NoticeDisconnection: target, gameover and connected all untouched. *)
Lemma NoticeDisconnectionTargetNotSelf : ∀ [s s' pl1]
  (H1 : PlayerCount > 1 → NoWinner s → ∀ pl, target s pl ≠ pl)
  (H2 : NoticeDisconnection pl1 s = Some s')
  (H3 : PlayerCount > 1) (H4 : NoWinner s'), ∀ pl, target s' pl ≠ pl.
Proof.
  intros.
  unfold NoticeDisconnection in H2.
  destruct (! connected s pl1 && connectedView s pl1 pl1); [ inject H2 | discriminate H2].
  assert (H5 : target s' = target s) by now rewrite <- H2.
  assert (H6 : ∀ q, gameover s' q = gameover s q)
    by (intro; unfold gameover; now rewrite <- H2).
  assert (H7 : ∀ q, connected s' q = connected s q) by (intro; now rewrite <- H2).
  rewrite H5.
  apply H1; [exact H3 |].
  destruct H4 as [q1 [q2 [H8 [H9 H10]]]].
  exists q1, q2; repeat split.
  - exact H8.
  - unfold Playing in *; rewrite <- (H6 q1), <- (H7 q1); exact H9.
  - unfold Playing in *; rewrite <- (H6 q2), <- (H7 q2); exact H10.
Qed.

Lemma StutterTargetNotSelf : ∀ [s s']
  (H1 : PlayerCount > 1 → NoWinner s → ∀ pl, target s pl ≠ pl)
  (H2 : Some s = Some s')
  (H3 : PlayerCount > 1) (H4 : NoWinner s'), ∀ pl, target s' pl ≠ pl.
Proof. intros; inject H2; rewrite <- H2 in H4 |- *; exact (H1 H3 H4 pl). Qed.

Lemma NextTargetNotSelf : ∀ [pl1 e s s']
  (H1 : PlayerCount > 1 → NoWinner s → ∀ pl, target s pl ≠ pl)
  (H2 : ViewSound s)
  (H2' : MessageSound s)
  (H3 : Next pl1 e s = Some s')
  (H3 : PlayerCount > 1) (H4 : NoWinner s'), ∀ pl, target s' pl ≠ pl.
Proof.
  intros.
  destruct e in H3; simpl in H3; (
    eapp MovePieceTargetNotSelf || eapp RotatePieceTargetNotSelf ||
    eapp FixPieceTargetNotSelf || eapp FallStepTargetNotSelf ||
    eapp HoldPieceTargetNotSelf || eapp DropPieceTargetNotSelf ||
    eapp RotateKickPieceTargetNotSelf || eapp ReceiveMessageTargetNotSelf ||
    eapp DisconnectPlayerTargetNotSelf || eapp NoticeDisconnectionTargetNotSelf ||
    eapp StutterTargetNotSelf).
Qed.

Theorem SpecTargetNotSelf :
   (∀ bags H, PlayerCount > 1 → NoWinner (Init bags H) → ∀ pl, target (Init bags H) pl ≠ pl)
 ∧ (∀ [pl1 e s s']
      (H1 : PlayerCount > 1 → NoWinner s → ∀ pl, target s pl ≠ pl)
      (H2 : ViewSound s)
      (H2' : MessageSound s)
      (H3 : Next pl1 e s = Some s'),
      PlayerCount > 1 → NoWinner s' → ∀ pl, target s' pl ≠ pl).
Proof. split; (exact InitTargetNotSelf || exact NextTargetNotSelf). Qed.


(* ========================================================================= *)
(* TargetPlaying                                                             *)
(* ========================================================================= *)

(* Init: target pl = PlayerNext pl ≠ pl (TargetNotSelf), so the observed cell
is not the diagonal one Init's own gameoverView special-cases, giving false;
connectedView is the constant PlayerCount >? 1, true by H1. *)
Lemma InitTargetPlaying : ∀ bags H,
  PlayerCount > 1 → NoWinner (Init bags H) → ∀ pl, PlayingView (Init bags H) pl (target (Init bags H) pl) = true.
Proof.
  intros bags H H1 H2 pl.
  assert (H3 : target (Init bags H) pl ≠ pl)
    by exact (InitTargetNotSelf bags H H1 H2 pl).
  simpl in H3.
  unfold PlayingView; simpl.
  apply andb_true_iff; split.
  - apply negb_true_iff.
    destruct (PlayerEqb (PlayerNext pl) pl) eqn: H4; [ | reflexivity].
    apply PlayerEqbEq1 in H4; exfalso; exact (H3 H4).
  - lia.
Qed.

(* Move/Rotate/Hold/RotateKick (via UpdatePlayer): target untouched, and the
only gameoverView cell that can move is pl1's own diagonal (pl1, pl1) (never
the cell (pl, target s pl) being read, since target s pl1 ≠ pl1 (TargetNotSelf).
connectedView is untouched entirely). *)
Lemma GuardedUpdateTargetPlaying : ∀ [A s s' pl1] [f : A → option T6.State] [x : A]
  (HTNS : target s pl1 ≠ pl1)
  (H1 : (if ! WinnerMulti s pl1 then option_map (UpdatePlayer s pl1) (f x) else None) = Some s'),
  ∀ pl, PlayingView s' pl (target s' pl) = PlayingView s pl (target s pl).
Proof.
  intros.
  rewrite (GuardedUpdateTargetNotSelf H1 pl).
  apply IfSome, T5P.OptionMapSome in H1.
  destruct H1 as [s6' [_ E]].
  unfold PlayingView; rewrite <- E; simpl.
  destruct (PlayerEqb pl pl1) eqn: Hp; simpl.
  - apply PlayerEqbEq1 in Hp; subst pl.
    destruct (PlayerEqb (target s pl1) pl1) eqn: Ht; simpl.
    + apply PlayerEqbEq1 in Ht; exfalso; exact (HTNS Ht).
    + reflexivity.
  - reflexivity.
Qed.

Lemma MovePieceTargetPlaying : ∀ [s s' pl1 dyx]
  (H1 : PlayerCount > 1 → NoWinner s → ∀ pl, PlayingView s pl (target s pl) = true)
  (HTNS : PlayerCount > 1 → NoWinner s → ∀ pl, target s pl ≠ pl)
  (H2 : MovePiece pl1 dyx s = Some s')
  (H3 : PlayerCount > 1) (H4 : NoWinner s'), ∀ pl, PlayingView s' pl (target s' pl) = true.
Proof.
  intros.
  assert (H5 : NoWinner s)
    by exact (NoWinnerBackward (λ pl2, MovePieceGameoverMonotone H2) (λ pl2, MovePieceConnectedMonotone H2) H4).
  rewrite (GuardedUpdateTargetPlaying (HTNS H3 H5 pl1) H2 pl).
  exact (H1 H3 H5 pl).
Qed.

Lemma RotatePieceTargetPlaying : ∀ [s s' pl1 dyx]
  (H1 : PlayerCount > 1 → NoWinner s → ∀ pl, PlayingView s pl (target s pl) = true)
  (HTNS : PlayerCount > 1 → NoWinner s → ∀ pl, target s pl ≠ pl)
  (H2 : RotatePiece pl1 dyx s = Some s')
  (H3 : PlayerCount > 1) (H4 : NoWinner s'), ∀ pl, PlayingView s' pl (target s' pl) = true.
Proof.
  intros.
  assert (H5 : NoWinner s)
    by exact (NoWinnerBackward (λ pl2, RotatePieceGameoverMonotone H2) (λ pl2, RotatePieceConnectedMonotone H2) H4).
  rewrite (GuardedUpdateTargetPlaying (HTNS H3 H5 pl1) H2 pl).
  exact (H1 H3 H5 pl).
Qed.

Lemma HoldPieceTargetPlaying : ∀ [s s' pl1 holes H1' bagNew H2']
  (H1 : PlayerCount > 1 → NoWinner s → ∀ pl, PlayingView s pl (target s pl) = true)
  (HTNS : PlayerCount > 1 → NoWinner s → ∀ pl, target s pl ≠ pl)
  (H2 : HoldPiece pl1 holes H1' bagNew H2' s = Some s')
  (H3 : PlayerCount > 1) (H4 : NoWinner s'), ∀ pl, PlayingView s' pl (target s' pl) = true.
Proof.
  intros.
  assert (H5 : NoWinner s)
    by exact (NoWinnerBackward (λ pl2, HoldPieceGameoverMonotone H2) (λ pl2, HoldPieceConnectedMonotone H2) H4).
  rewrite (GuardedUpdateTargetPlaying (HTNS H3 H5 pl1) H2 pl).
  exact (H1 H3 H5 pl).
Qed.

Lemma RotateKickPieceTargetPlaying : ∀ [s s' pl1 cw]
  (H1 : PlayerCount > 1 → NoWinner s → ∀ pl, PlayingView s pl (target s pl) = true)
  (HTNS : PlayerCount > 1 → NoWinner s → ∀ pl, target s pl ≠ pl)
  (H2 : RotateKickPiece pl1 cw s = Some s')
  (H3 : PlayerCount > 1) (H4 : NoWinner s'), ∀ pl, PlayingView s' pl (target s' pl) = true.
Proof.
  intros.
  assert (H5 : NoWinner s)
    by exact (NoWinnerBackward (λ pl2, RotateKickPieceGameoverMonotone H2)
      (λ pl2, RotateKickPieceConnectedMonotone H2) H4).
  rewrite (GuardedUpdateTargetPlaying (HTNS H3 H5 pl1) H2 pl).
  exact (H1 H3 H5 pl).
Qed.

(* FixPiece: single-player branch is vacuous, same as FixPieceTargetNotSelf.
Multiplayer, no redirect: same cell-exclusion argument as GuardedUpdateTargetPlaying,
using TargetNotSelf(s) to rule out the (pl1, pl1) diagonal. Multiplayer, redirect
(pl = pl1): the result R is ≠ pl1 by FixPieceTargetNotSelf (reused, not re-derived);
NextTargetAuxPlayingWhenNotSelf then gives FP.PlayingView' s pl1 s6' holes R = true
directly from the search's own construction (no cyclic-permutation search needed,
unlike TargetNotSelf); and FP.PlayingView' is definitionally in sync with the real
post-state PlayingView at R, since gameoverView' only special-cases the (pl1, pl1)
cell FP.GameoverView' already special-cases identically, and connectedView is
untouched. *)
Section Player.
Open Scope player_scope.

Lemma FixPieceTargetPlaying : ∀ [s s' pl1 holes H1' bagNew H2']
  (H1 : PlayerCount > 1 → NoWinner s → ∀ pl, PlayingView s pl (target s pl) = true)
  (HTNS : PlayerCount > 1 → NoWinner s → ∀ pl, target s pl ≠ pl)
  (HVS : ViewSound s)
  (H3 : FixPiece pl1 holes H1' bagNew H2' s = Some s')
  (H4 : PlayerCount > 1) (H5 : NoWinner s'), ∀ pl, PlayingView s' pl (target s' pl) = true.
Proof.
  intros.
  assert (H6 : NoWinner s)
    by exact (NoWinnerBackward (λ pl2, FixPieceGameoverMonotone H3) (λ pl2, FixPieceConnectedMonotone H3) H5).
  assert (H6' : ∀ pl0, target s' pl0 ≠ pl0)
    by exact (FixPieceTargetNotSelf HTNS HVS H3 H4 H5).
  assert (H3' := H3); unfold FixPiece in H3'.
  destruct (! WinnerMulti s pl1) eqn: H7; [ | discriminate H3'].
  destruct (T6.FixPiece bagNew H2' (s6 s pl1)) as [s6' |] eqn: H8; [ | discriminate H3'].
  unfold option_map in H3'; inject H3'.
  destruct ((PlayerCount =? 1)%nat) eqn: H9.
  - apply Nat.eqb_eq in H9; lia.
  - set (gameover' := FP.Gameover' s pl1 s6' holes) in *.
    set (remGenGarbage := FP.RemGenGarbage s pl1 s6') in *.
    assert (H10 : ∀ pl2, target s' pl2 =
        if PlayerEqb pl2 pl1 && (0 <? remGenGarbage)%nat && ! gameover'
        then NextTarget (FP.PlayingView' s pl1 s6' holes) pl1 (target s pl1)
        else target s pl2)
      by (intros; now rewrite <- H3').
    assert (H10gv : gameoverView s' = λ obs obsd,
        if PlayerEqb obs pl1 && PlayerEqb obsd pl1 then gameover' else gameoverView s obs obsd)
      by (now rewrite <- H3').
    assert (H10cv : connectedView s' = connectedView s)
      by (now rewrite <- H3').
    rewrite (H10 pl).
    destruct (PlayerEqb pl pl1 && (0 <? remGenGarbage)%nat && ! gameover') eqn: H11.
    + (* redirect: pl = pl1 *)
      apply andb_true_iff in H11 as [H11a H11b].
      apply andb_true_iff in H11a as [H11c H11d].
      apply PlayerEqbEq1 in H11c; subst pl.
      set (R := NextTarget (FP.PlayingView' s pl1 s6' holes) pl1 (target s pl1)) in *.
      assert (H12 : target s' pl1 = R)
        by (rewrite (H10 pl1), (PlayerEqbReflexive pl1), H11d, H11b; reflexivity).
      assert (H13 : R ≠ pl1) by (rewrite <- H12; exact (H6' pl1)).
      assert (H14 : FP.PlayingView' s pl1 s6' holes R = true). {
        unfold R, NextTarget in H13 |- *.
        exact (NextTargetAuxPlayingWhenNotSelf PlayerCount (FP.PlayingView' s pl1 s6' holes) pl1
                 (target s pl1) H13).
      }
      unfold FP.PlayingView', FP.GameoverView' in H14.
      destruct (PlayerEqb R pl1) eqn: H15.
      * apply PlayerEqbEq1 in H15; exfalso; exact (H13 H15).
      * unfold PlayingView; rewrite H10gv, H10cv; simpl.
        rewrite (PlayerEqbReflexive pl1); simpl.
        rewrite H15.
        exact H14.
    + (* no redirect: target s' pl = target s pl *)
      unfold PlayingView; rewrite H10gv, H10cv; simpl.
      destruct (PlayerEqb pl pl1) eqn: Hp; simpl.
      * apply PlayerEqbEq1 in Hp; subst pl.
        destruct (PlayerEqb (target s pl1) pl1) eqn: Ht; simpl.
        -- apply PlayerEqbEq1 in Ht; exfalso; exact ((HTNS H4 H6 pl1) Ht).
        -- exact (H1 H4 H6 pl1).
      * exact (H1 H4 H6 pl).
Qed.

End Player.

(* Forward to MovePiece and FixPiece. *)
Lemma FallStepTargetPlaying : ∀ [s s' pl1 holes H1' bagNew H2']
  (H1 : PlayerCount > 1 → NoWinner s → ∀ pl, PlayingView s pl (target s pl) = true)
  (HTNS : PlayerCount > 1 → NoWinner s → ∀ pl, target s pl ≠ pl)
  (HVS : ViewSound s)
  (H3 : FallStep pl1 holes H1' bagNew H2' s = Some s')
  (H4 : PlayerCount > 1) (H5 : NoWinner s'), ∀ pl, PlayingView s' pl (target s' pl) = true.
Proof.
  intros; unfold FallStep in H3.
  destruct (! WinnerMulti s pl1) in H3.
  - destruct (MovePiece pl1 (-1, 0)%Z s) eqn: H6.
    + rewrite H3 in H6.
      exact (MovePieceTargetPlaying H1 HTNS H6 H4 H5 pl).
    + exact (FixPieceTargetPlaying H1 HTNS HVS H3 H4 H5 pl).
  - discriminate H3.
Qed.

Lemma NewPieceYXStatePlayingViewUnchanged : ∀ s pyxNew pl1 pl2 pl3,
  PlayingView (NewPieceYXState pyxNew pl1 s) pl2 pl3 = PlayingView s pl2 pl3.
Proof. intros; unfold PlayingView, NewPieceYXState, UnchangedT7Part; reflexivity. Qed.

Lemma NewPieceYXStateTargetPlaying : ∀ [s pyxNew pl1]
  (H1 : PlayerCount > 1 → NoWinner s → ∀ pl, PlayingView s pl (target s pl) = true)
  (H2 : PlayerCount > 1) (H3 : NoWinner (NewPieceYXState pyxNew pl1 s)),
  ∀ pl, PlayingView (NewPieceYXState pyxNew pl1 s) pl (target (NewPieceYXState pyxNew pl1 s) pl) = true.
Proof.
  intros.
  rewrite NewPieceYXStateTargetUnchanged, NewPieceYXStatePlayingViewUnchanged.
  apply H1; [exact H2 |].
  destruct H3 as [q1 [q2 [H4 [H5 H6]]]].
  exists q1, q2; repeat split.
  - exact H4.
  - unfold Playing in *; rewrite (NewPieceYXStateGameoverUnchanged q1), (NewPieceYXStateConnectedUnchanged s pyxNew pl1) in H5.
    exact H5.
  - unfold Playing in *; rewrite (NewPieceYXStateGameoverUnchanged q2), (NewPieceYXStateConnectedUnchanged s pyxNew pl1) in H6.
    exact H6.
Qed.

Lemma DropPieceTargetPlaying : ∀ [s s' pl1 holes H1' bagNew H2']
  (H1 : PlayerCount > 1 → NoWinner s → ∀ pl, PlayingView s pl (target s pl) = true)
  (HTNS : PlayerCount > 1 → NoWinner s → ∀ pl, target s pl ≠ pl)
  (HVS : ViewSound s)
  (H3 : DropPiece pl1 holes H1' bagNew H2' s = Some s')
  (H4 : PlayerCount > 1) (H5 : NoWinner s'), ∀ pl, PlayingView s' pl (target s' pl) = true.
Proof.
  intros.
  exact (FixPieceTargetPlaying (NewPieceYXStateTargetPlaying H1) (NewPieceYXStateTargetNotSelf HTNS)
           (NewPieceYXStateViewSound HVS) H3 H4 H5 pl).
Qed.

(* ReceiveMessage: GarbageMessage leaves target, gameoverView and connectedView
all untouched. GameoverMessage/DisconnectMessage: outside the redirect, the
touched cell is (pl1, pl2), which the branch's own falsity already excludes
whenever the observer is pl1 (and is irrelevant otherwise); inside the
redirect, the same argument as FixPiece's own redirect applies, with the
result R's non-selfhood coming from ReceiveMessageTargetNotSelf (reused, not
re-derived) and the search's own construction giving R ≠ pl2 too (the search
function hardwires playing pl2 = false, so a result satisfying playing = true
cannot be pl2). *)
Lemma ReceiveMessageTargetPlaying : ∀ [s s' pl1 pl2]
  (H1 : PlayerCount > 1 → NoWinner s → ∀ pl, PlayingView s pl (target s pl) = true)
  (HTNS : PlayerCount > 1 → NoWinner s → ∀ pl, target s pl ≠ pl)
  (HVS : ViewSound s)
  (HMS : MessageSound s)
  (H4 : ReceiveMessage pl1 pl2 s = Some s')
  (H5 : PlayerCount > 1) (H6 : NoWinner s'), ∀ pl, PlayingView s' pl (target s' pl) = true.
Proof.
  intros.
  assert (H6' : ∀ pl0, target s' pl0 ≠ pl0)
    by exact (ReceiveMessageTargetNotSelf HTNS HVS HMS H4 H5 H6).
  unfold ReceiveMessage in H4.
  destruct (connected s pl1) eqn: H7; [ | discriminate H4].
  destruct (messages s pl2 pl1) as [|m ms] eqn: H8; [discriminate H4 |].
  assert (H9 : ∀ q, gameover s' q = gameover s q)
    by (intro; destruct m; inject H4; unfold gameover; now rewrite <- H4).
  assert (H10 : ∀ q, connected s' q = connected s q)
    by (intro; destruct m; inject H4; now rewrite <- H4).
  assert (H11 : NoWinner s). {
    destruct H6 as [q1 [q2 [H12 [H13 H14]]]].
    exists q1, q2; repeat split.
    - exact H12.
    - unfold Playing in *; rewrite <- (H9 q1), <- (H10 q1); exact H13.
    - unfold Playing in *; rewrite <- (H9 q2), <- (H10 q2); exact H14.
  }
  destruct m eqn: Hm.
  - (* GarbageMessage *)
    assert (H12 : target s' = target s) by (inject H4; now rewrite <- H4).
    assert (H12gv : gameoverView s' = gameoverView s) by (inject H4; now rewrite <- H4).
    assert (H12cv : connectedView s' = connectedView s) by (inject H4; now rewrite <- H4).
    rewrite H12; unfold PlayingView; rewrite H12gv, H12cv.
    exact (H1 H5 H11 pl).
  - (* GameoverMessage *)
    inject H4.
    assert (H12 : ∀ pl3, target s' pl3 =
        if PlayerEqb pl3 pl1 && PlayerEqb (target s pl1) pl2 then
          NextTarget (λ pl4, if PlayerEqb pl4 pl2 then false else PlayingView s pl1 pl4) pl1 pl2
        else target s pl3)
      by (intro; now rewrite <- H4).
    assert (H12gv : gameoverView s' = λ obs obsd,
        if PlayerEqb obs pl1 && PlayerEqb obsd pl2 then true else gameoverView s obs obsd)
      by (now rewrite <- H4).
    assert (H12cv : connectedView s' = connectedView s)
      by (now rewrite <- H4).
    rewrite (H12 pl).
    destruct (PlayerEqb pl pl1 && PlayerEqb (target s pl1) pl2) eqn: H13.
    + (* redirect: pl = pl1 *)
      apply andb_true_iff in H13 as [H13a H13b].
      apply PlayerEqbEq1 in H13a; subst pl.
      set (R := NextTarget (λ pl4, if PlayerEqb pl4 pl2 then false else PlayingView s pl1 pl4) pl1 pl2) in *.
      assert (H14 : target s' pl1 = R)
        by (rewrite (H12 pl1), (PlayerEqbReflexive pl1), H13b; reflexivity).
      assert (H15 : R ≠ pl1) by (rewrite <- H14; exact (H6' pl1)).
      assert (H16 : (λ pl4, if PlayerEqb pl4 pl2 then false else PlayingView s pl1 pl4) R = true). {
        unfold R, NextTarget in H15 |- *.
        exact (NextTargetAuxPlayingWhenNotSelf PlayerCount
                 (λ pl4, if PlayerEqb pl4 pl2 then false else PlayingView s pl1 pl4) pl1 pl2 H15).
      }
      simpl in H16.
      destruct (PlayerEqb R pl2) eqn: H17; [ discriminate H16 | ].
      unfold PlayingView; rewrite H12gv, H12cv; simpl.
      rewrite (PlayerEqbReflexive pl1); simpl.
      rewrite H17.
      exact H16.
    + (* no redirect *)
      unfold PlayingView; rewrite H12gv, H12cv; simpl.
      destruct (PlayerEqb pl pl1) eqn: Hp; simpl.
      * apply PlayerEqbEq1 in Hp; subst pl.
        (* By this point H13's first conjunct has already collapsed to the
        literal `true`, so it reads `true && (target s pl1 =? pl2) = false`
        rather than the syntactic form used to derive it; reduce it before
        matching it against the goal's own (already-reduced) condition. *)
        simpl in H13; rewrite H13; simpl.
        exact (H1 H5 H11 pl1).
      * exact (H1 H5 H11 pl).
  - (* DisconnectMessage: symmetric, via connectedView instead of gameoverView *)
    inject H4.
    assert (H12 : ∀ pl3, target s' pl3 =
        if PlayerEqb pl3 pl1 && PlayerEqb (target s pl1) pl2 then
          NextTarget (λ pl4, if PlayerEqb pl4 pl2 then false else PlayingView s pl1 pl4) pl1 pl2
        else target s pl3)
      by (intro; now rewrite <- H4).
    assert (H12gv : gameoverView s' = gameoverView s)
      by (now rewrite <- H4).
    assert (H12cv : connectedView s' = λ pl3 pl4,
        if PlayerEqb pl3 pl1 && PlayerEqb pl4 pl2 then false else connectedView s pl3 pl4)
      by (now rewrite <- H4).
    rewrite (H12 pl).
    destruct (PlayerEqb pl pl1 && PlayerEqb (target s pl1) pl2) eqn: H13.
    + (* redirect: pl = pl1 *)
      apply andb_true_iff in H13 as [H13a H13b].
      apply PlayerEqbEq1 in H13a; subst pl.
      set (R := NextTarget (λ pl4, if PlayerEqb pl4 pl2 then false else PlayingView s pl1 pl4) pl1 pl2) in *.
      assert (H14 : target s' pl1 = R)
        by (rewrite (H12 pl1), (PlayerEqbReflexive pl1), H13b; reflexivity).
      assert (H15 : R ≠ pl1) by (rewrite <- H14; exact (H6' pl1)).
      assert (H16 : (λ pl4, if PlayerEqb pl4 pl2 then false else PlayingView s pl1 pl4) R = true). {
        unfold R, NextTarget in H15 |- *.
        exact (NextTargetAuxPlayingWhenNotSelf PlayerCount
                 (λ pl4, if PlayerEqb pl4 pl2 then false else PlayingView s pl1 pl4) pl1 pl2 H15).
      }
      simpl in H16.
      destruct (PlayerEqb R pl2) eqn: H17; [ discriminate H16 | ].
      unfold PlayingView; rewrite H12gv, H12cv; simpl.
      rewrite (PlayerEqbReflexive pl1); simpl.
      rewrite H17.
      exact H16.
    + (* no redirect *)
      unfold PlayingView; rewrite H12gv, H12cv; simpl.
      destruct (PlayerEqb pl pl1) eqn: Hp; simpl.
      * apply PlayerEqbEq1 in Hp; subst pl.
        simpl in H13; rewrite H13; simpl.
        exact (H1 H5 H11 pl1).
      * exact (H1 H5 H11 pl).
Qed.

(* DisconnectPlayer: target, gameoverView and connectedView are all literally
unchanged (only connected/messages move); connected is monotone, so
NoWinner s' -> NoWinner s still holds. *)
Lemma DisconnectPlayerTargetPlaying : ∀ [s s' pl1]
  (H1 : PlayerCount > 1 → NoWinner s → ∀ pl, PlayingView s pl (target s pl) = true)
  (H2 : DisconnectPlayer pl1 s = Some s')
  (H3 : PlayerCount > 1) (H4 : NoWinner s'), ∀ pl, PlayingView s' pl (target s' pl) = true.
Proof.
  intros.
  assert (H5 := H2); unfold DisconnectPlayer in H5.
  destruct (connected s pl1) eqn: H6; [ inject H5 | discriminate H5].
  assert (H7 : target s' = target s) by now rewrite <- H5.
  assert (H8 : gameoverView s' = gameoverView s) by now rewrite <- H5.
  assert (H9 : connectedView s' = connectedView s) by now rewrite <- H5.
  assert (H10 : ∀ pl2, gameover s' pl2 = gameover s pl2)
    by (intro; unfold gameover; now rewrite <- H5).
  rewrite H7; unfold PlayingView; rewrite H8, H9.
  apply H1; [exact H3 |].
  exact (NoWinnerBackward (λ pl2 H11, eq_trans (H10 pl2) H11)
           (λ pl2, DisconnectPlayerConnectedMonotone H2) H4).
Qed.

(* NoticeDisconnection: target and gameoverView are untouched; connectedView
only moves at the (pl1, pl1) diagonal — never the cell (pl, target s pl)
being read, since target s pl1 ≠ pl1 (TargetNotSelf). Same shape as
GuardedUpdateTargetPlaying, on connectedView instead of gameoverView. *)
Lemma NoticeDisconnectionTargetPlaying : ∀ [s s' pl1]
  (H1 : PlayerCount > 1 → NoWinner s → ∀ pl, PlayingView s pl (target s pl) = true)
  (HTNS : PlayerCount > 1 → NoWinner s → ∀ pl, target s pl ≠ pl)
  (H2 : NoticeDisconnection pl1 s = Some s')
  (H3 : PlayerCount > 1) (H4 : NoWinner s'), ∀ pl, PlayingView s' pl (target s' pl) = true.
Proof.
  intros.
  assert (H5 : NoWinner s)
    by exact (NoWinnerBackward (λ pl2, NoticeDisconnectionGameoverMonotone H2)
                (λ pl2, NoticeDisconnectionConnectedMonotone H2) H4).
  unfold NoticeDisconnection in H2.
  destruct (! connected s pl1 && connectedView s pl1 pl1) eqn: H6; [ inject H2 | discriminate H2].
  assert (H7 : target s' = target s) by now rewrite <- H2.
  assert (H8 : gameoverView s' = gameoverView s) by now rewrite <- H2.
  assert (H9 : connectedView s' = λ pl2 pl3,
      if PlayerEqb pl2 pl1 && PlayerEqb pl3 pl1 then false else connectedView s pl2 pl3)
    by now rewrite <- H2.
  rewrite H7; unfold PlayingView; rewrite H8, H9; simpl.
  destruct (PlayerEqb pl pl1) eqn: Hp; simpl.
  - apply PlayerEqbEq1 in Hp; subst pl.
    destruct (PlayerEqb (target s pl1) pl1) eqn: Ht; simpl.
    + apply PlayerEqbEq1 in Ht; exfalso; exact ((HTNS H3 H5 pl1) Ht).
    + exact (H1 H3 H5 pl1).
  - exact (H1 H3 H5 pl).
Qed.

Lemma StutterTargetPlaying : ∀ [s s']
  (H1 : PlayerCount > 1 → NoWinner s → ∀ pl, PlayingView s pl (target s pl) = true)
  (H2 : Some s = Some s')
  (H3 : PlayerCount > 1) (H4 : NoWinner s'), ∀ pl, PlayingView s' pl (target s' pl) = true.
Proof. intros; inject H2; rewrite <- H2 in H4 |- *; exact (H1 H3 H4 pl). Qed.

Lemma NextTargetPlaying : ∀ [pl1 e s s']
  (H1 : PlayerCount > 1 → NoWinner s → ∀ pl, PlayingView s pl (target s pl) = true)
  (HTNS : PlayerCount > 1 → NoWinner s → ∀ pl, target s pl ≠ pl)
  (H2 : ViewSound s)
  (H2' : MessageSound s)
  (H3 : Next pl1 e s = Some s')
  (H3 : PlayerCount > 1) (H4 : NoWinner s'), ∀ pl, PlayingView s' pl (target s' pl) = true.
Proof.
  intros.
  destruct e in H3; simpl in H3; (
    eapp MovePieceTargetPlaying || eapp RotatePieceTargetPlaying ||
    eapp FixPieceTargetPlaying || eapp FallStepTargetPlaying ||
    eapp HoldPieceTargetPlaying || eapp DropPieceTargetPlaying ||
    eapp RotateKickPieceTargetPlaying || eapp ReceiveMessageTargetPlaying ||
    eapp DisconnectPlayerTargetPlaying || eapp NoticeDisconnectionTargetPlaying ||
    eapp StutterTargetPlaying).
Qed.

Theorem SpecTargetPlaying :
   (∀ bags H, PlayerCount > 1 → NoWinner (Init bags H) → ∀ pl, PlayingView (Init bags H) pl (target (Init bags H) pl) = true)
 ∧ (∀ [pl1 e s s']
      (H1 : PlayerCount > 1 → NoWinner s → ∀ pl, PlayingView s pl (target s pl) = true)
      (HTNS : PlayerCount > 1 → NoWinner s → ∀ pl, target s pl ≠ pl)
      (H2 : ViewSound s)
      (H2' : MessageSound s)
      (H3 : Next pl1 e s = Some s'),
      PlayerCount > 1 → NoWinner s' → ∀ pl, PlayingView s' pl (target s' pl) = true).
Proof. split; (exact InitTargetPlaying || exact NextTargetPlaying). Qed.


(* ========================================================================= *)
(* S6Correct                                                                 *)
(* ========================================================================= *)

(* T6.Correct implies CorrectWithoutGameover, and (separately) the weak
Gameover direction. *)
Lemma T6CorrectImpliesCorrectWithoutGameover : ∀ s6,
  T6.Correct s6 → T6.CorrectWithoutGameover s6.
Proof.
  intros s6 H.
  unfold T6.Correct, T5.Correct, T4.Correct, T3.Correct, T2.Correct, T1.Correct,
    T6.CorrectWithoutGameover, T5.CorrectWithoutGameover, T4.CorrectWithoutGameover,
    T3.CorrectWithoutGameover, T2.CorrectWithoutGameover, T1.CorrectWithoutGameover in *.
  tauto.
Qed.

Lemma T6CorrectImpliesWeakGameover : ∀ s6,
  T6.Correct s6 → ForbiddenGrid ∩ T6.mg s6 ⊈ ∅ = true → T6.gameover s6 = true.
Proof.
  intros s6 H.
  unfold T6.Correct, T5.Correct, T4.Correct, T3.Correct, T2.Correct, T1.Correct,
    T1.Gameover, T6.gameover, T5.gameover, T4.gameover, T3.gameover, T2.gameover,
    T6.mg, T5.mg, T4.mg, T3.mg, T2.mg in *.
  tauto.
Qed.

(* Init: T6.Init already satisfies full T6.Correct (existing InitCorrect),
independently for every player. *)
Lemma InitS6Correct : ∀ bags H,
  S6Correct (Init bags H).
Proof.
  unfold S6Correct; intros.
  assert (H1 : T6.Correct (s6 (Init bags H) pl)) by exact (T6P.InitCorrect (bags pl) (H pl)).
  split.
  - exact (T6CorrectImpliesCorrectWithoutGameover _ H1).
  - unfold Gameover; exact (T6CorrectImpliesWeakGameover _ H1).
Qed.

(* Move/Rotate/Hold/RotateKick (via UpdatePlayer): the acting player's own s6
transfers CorrectWithoutGameover directly via the matching CorrectWithoutGameover
lemma (H4), with no need to reconstruct full T6.Correct at all; the weak
Gameover fact transfers because mg/gameover are themselves literally
unchanged by the operation (H5), so Gameover pl1 s' is the very same
proposition as Gameover pl1 s once mg/gameover are substituted. Every other
player's s6 is untouched by UpdatePlayer. *)
Lemma GuardedUpdateS6Correct : ∀ [A s s' pl1] [f : A → option T6.State] [x : A]
  (H1 : S6Correct s)
  (H3 : (if ! WinnerMulti s pl1 then option_map (UpdatePlayer s pl1) (f x) else None) = Some s')
  (H4 : ∀ s6'', T6.CorrectWithoutGameover (s6 s pl1) → Gameover pl1 s → f x = Some s6'' →
          T6.CorrectWithoutGameover s6'')
  (H5 : ∀ s6'', T6.CorrectWithoutGameover (s6 s pl1) → f x = Some s6'' →
          T6.mg s6'' = T6.mg (s6 s pl1) ∧ T6.gameover s6'' = T6.gameover (s6 s pl1)),
  S6Correct s'.
Proof.
  unfold S6Correct in *; intros.
  specialize H1 with pl; destruct H1 as [H1 H2].
  apply IfSome, T5P.OptionMapSome in H3.
  destruct H3 as [s6'' [H6 H7]].
  destruct (PlayerEqb pl pl1) eqn: H8.
  - apply PlayerEqbEq1 in H8; subst pl.
    assert (H9 : T6.CorrectWithoutGameover s6'') by exact (H4 s6'' H1 H2 H6).
    destruct (H5 s6'' H1 H6) as [Hmg Hgo].
    assert (H10 : s6 s' pl1 = s6'')
      by (rewrite <- H7; unfold UpdatePlayer; simpl; rewrite (PlayerEqbReflexive pl1); reflexivity).
    rewrite H10.
    split; [exact H9 | ].
    unfold Gameover, mg, gameover in *; rewrite H10, Hmg, Hgo; exact H2.
  - assert (H9 : s6 s' pl = s6 s pl)
      by (rewrite <- H7; unfold UpdatePlayer; simpl; rewrite H8; reflexivity).
    rewrite H9; split.
    + exact H1.
    + unfold Gameover, gameover, mg; rewrite H9; exact H2.
Qed.

Lemma MovePieceS6Correct : ∀ [s s' pl1 dyx]
  (H1 : S6Correct s)
  (H3 : MovePiece pl1 dyx s = Some s'),
  S6Correct s'.
Proof.
  intros.
  exact (GuardedUpdateS6Correct H1 H3
           (λ s6'' H4 _ H6, T5P.MovePieceCorrectWithoutGameover H4 H6)
           (λ s6'' _ H6, T5P.MovePieceMgGameoverUnchanged H6)).
Qed.

Lemma RotatePieceS6Correct : ∀ [s s' pl1 cw]
  (H1 : S6Correct s)
  (H3 : RotatePiece pl1 cw s = Some s'),
  S6Correct s'.
Proof.
  intros.
  exact (GuardedUpdateS6Correct H1 H3
           (λ s6'' H4 _ H6, T5P.RotatePieceCorrectWithoutGameover H4 H6)
           (λ s6'' _ H6, T5P.RotatePieceMgGameoverUnchanged H6)).
Qed.

Lemma HoldPieceS6Correct : ∀ [s s' pl1 holes H1' bagNew H2']
  (H1 : S6Correct s)
  (H3 : HoldPiece pl1 holes H1' bagNew H2' s = Some s'),
  S6Correct s'.
Proof.
  intros.
  exact (GuardedUpdateS6Correct H1 H3
           (λ s6'' H4 H5 H6, T5P.HoldPieceCorrectWithoutGameover H4 H5 H6)
           (λ s6'' _ H6, T5P.HoldPieceMgGameoverUnchanged H6)).
Qed.

Lemma RotateKickPieceS6Correct : ∀ [s s' pl1 cw]
  (H1 : S6Correct s)
  (H3 : RotateKickPiece pl1 cw s = Some s'),
  S6Correct s'.
Proof.
  intros.
  exact (GuardedUpdateS6Correct H1 H3
           (λ s6'' H4 _ H6, T6P.RotateKickPieceCorrectWithoutGameover H4 H6)
           (λ s6'' H4 H6, T6P.RotateKickPieceMgGameoverUnchanged H4 H6)).
Qed.

Lemma ReceiveMessageS6Correct : ∀ [s s' pl1 pl2]
  (H1 : S6Correct s)
  (H3 : ReceiveMessage pl1 pl2 s = Some s'),
  S6Correct s'.
Proof.
  unfold S6Correct; intros.
  unfold ReceiveMessage in H3.
  destruct (connected s pl1) eqn: H4; [ | discriminate H3].
  destruct (messages s pl2 pl1) as [|m ms] eqn: H5; [discriminate H3 |].
  destruct m eqn: Hm; inject H3;
    (assert (L2 : s6 s' pl = s6 s pl) by now rewrite <- H3);
    (assert (L1 : T6.CorrectWithoutGameover (s6 s' pl))
      by now pose proof (H1 pl) as L1_1; rewrite <- L2 in L1_1; tauto);
    (assert (L3 : Gameover pl s') by now unfold Gameover, gameover, mg; rewrite L2; apply H1);
    split; (exact L1 || exact L3).
Qed.

Lemma DisconnectPlayerS6Correct : ∀ [s s' pl1]
  (H1 : S6Correct s)
  (H3 : DisconnectPlayer pl1 s = Some s'),
  S6Correct s'.
Proof.
  unfold S6Correct in *; intros.
  unfold DisconnectPlayer in H3.
  destruct (connected s pl1) eqn: H4; [ inject H3 | discriminate H3].
  assert (H5 : s6 s' pl = s6 s pl) by (now rewrite <- H3).
  rewrite H5; split.
  - apply H1.
  - unfold Gameover, gameover, mg in *; rewrite H5; apply H1.
Qed.

Lemma NoticeDisconnectionS6Correct : ∀ [s s' pl1]
  (H1 : S6Correct s)
  (H3 : NoticeDisconnection pl1 s = Some s'),
  S6Correct s'.
Proof.
  unfold S6Correct in *; intros.
  unfold NoticeDisconnection in H3.
  destruct (! connected s pl1 && connectedView s pl1 pl1) eqn: H4; [ inject H3 | discriminate H3].
  assert (H5 : s6 s' pl = s6 s pl) by (now rewrite <- H3).
  rewrite H5; split.
  - apply H1.
  - unfold Gameover, gameover, mg in *; rewrite H5; apply H1.
Qed.

Lemma StutterS6Correct : ∀ [s s']
  (H1 : S6Correct s)
  (H3 : Some s = Some s'),
  S6Correct s'.
Proof. unfold S6Correct in *; intros; inject H3; rewrite <- H3; split; apply H1. Qed.

(* FixPiece and its materializing-branch grid-shape lemma below; the sequel
(FixPiece's remaining content lemmas, FallStep, DropPiece, and the final
Next/Spec wrap-up) follows once the fresh-piece chain for PieceOnFreeBlocks
and NoFullLine is in place. *)

#[local] Open Scope Z_scope.

(* CroppedMg' keeps exactly mg s6''s own box: the mask's own bbox matches
shiftedMg's (so intersecting with it doesn't crop anything), and shiftedMg
∪ garbageGrid then ∩ Full(mg s6') clamps back down to mg s6''s original
height/width/origin regardless of remGarbage, by direct Z arithmetic on
GridUnion/GridIntersect's min/max formulas. *)
Lemma FPMgShiftedMaskBox : ∀ (g : Grid) (thresh : ℤ),
    Y (g ∩ {| L := λ y _, (thresh ≤? y)%Z; HW := HW g; YX := YX g |}) = Y g
  ∧ X (g ∩ {| L := λ y _, (thresh ≤? y)%Z; HW := HW g; YX := YX g |}) = X g
  ∧ H (g ∩ {| L := λ y _, (thresh ≤? y)%Z; HW := HW g; YX := YX g |}) = H g
  ∧ W (g ∩ {| L := λ y _, (thresh ≤? y)%Z; HW := HW g; YX := YX g |}) = W g.
Proof.
  intros g thresh.
  assert (EY : Y (g ∩ {| L := λ y _, thresh ≤? y; HW := HW g; YX := YX g |})
             = Z.max (Y g) (Y g)) by reflexivity.
  assert (EX : X (g ∩ {| L := λ y _, thresh ≤? y; HW := HW g; YX := YX g |})
             = Z.max (X g) (X g)) by reflexivity.
  assert (EH : H (g ∩ {| L := λ y _, thresh ≤? y; HW := HW g; YX := YX g |})
             = Z.min (Y g + H g) (Y g + H g) - Z.max (Y g) (Y g)) by reflexivity.
  assert (EW : W (g ∩ {| L := λ y _, thresh ≤? y; HW := HW g; YX := YX g |})
             = Z.min (X g + W g) (X g + W g) - Z.max (X g) (X g)) by reflexivity.
  repeat split; [rewrite EY | rewrite EX | rewrite EH | rewrite EW]; lia.
Qed.

(* Single-layer grid-box facts, kept fully generic (never touching a specific
grid's own definition) so that computing FPCroppedMgBox stays a sequence of
tiny, independent steps instead of one simpl call over the whole nested
GridUnion/GridIntersect/GridTranslate stack -- which duplicates subterms at
every layer (each H/W/Y/X reference re-expands the grid literal it's applied
to) and blows up exponentially with the nesting depth. *)
Lemma GridUnionY : ∀ g1 g2, Y (g1 ∪ g2) = Z.min (Y g1) (Y g2). Proof. reflexivity. Qed.
Lemma GridUnionX : ∀ g1 g2, X (g1 ∪ g2) = Z.min (X g1) (X g2). Proof. reflexivity. Qed.
Lemma GridUnionH : ∀ g1 g2,
  H (g1 ∪ g2) = Z.max (Y g1 + H g1) (Y g2 + H g2) - Z.min (Y g1) (Y g2).
Proof. reflexivity. Qed.
Lemma GridUnionW : ∀ g1 g2,
  W (g1 ∪ g2) = Z.max (X g1 + W g1) (X g2 + W g2) - Z.min (X g1) (X g2).
Proof. reflexivity. Qed.

Lemma GridIntersectY : ∀ g1 g2, Y (g1 ∩ g2) = Z.max (Y g1) (Y g2). Proof. reflexivity. Qed.
Lemma GridIntersectX : ∀ g1 g2, X (g1 ∩ g2) = Z.max (X g1) (X g2). Proof. reflexivity. Qed.
Lemma GridIntersectH : ∀ g1 g2,
  H (g1 ∩ g2) = Z.min (Y g1 + H g1) (Y g2 + H g2) - Z.max (Y g1) (Y g2).
Proof. reflexivity. Qed.
Lemma GridIntersectW : ∀ g1 g2,
  W (g1 ∩ g2) = Z.min (X g1 + W g1) (X g2 + W g2) - Z.max (X g1) (X g2).
Proof. reflexivity. Qed.

Lemma GridTranslateY : ∀ g d, Y (g ⊕ d) = Y g + fst d. Proof. intros g d; destruct d; reflexivity. Qed.
Lemma GridTranslateX : ∀ g d, X (g ⊕ d) = X g + snd d. Proof. intros g d; destruct d; reflexivity. Qed.
Lemma GridTranslateH : ∀ g d, H (g ⊕ d) = H g. Proof. intros g d; destruct d; reflexivity. Qed.
Lemma GridTranslateW : ∀ g d, W (g ⊕ d) = W g. Proof. intros g d; destruct d; reflexivity. Qed.

Lemma GridFullY : ∀ g, Y (Full g) = Y g. Proof. reflexivity. Qed.
Lemma GridFullX : ∀ g, X (Full g) = X g. Proof. reflexivity. Qed.
Lemma GridFullH : ∀ g, H (Full g) = H g. Proof. reflexivity. Qed.
Lemma GridFullW : ∀ g, W (Full g) = W g. Proof. reflexivity. Qed.

Lemma GarbageGridY : ∀ n holes w, Y (GarbageGrid n holes w) = 0. Proof. reflexivity. Qed.
Lemma GarbageGridX : ∀ n holes w, X (GarbageGrid n holes w) = 0. Proof. reflexivity. Qed.
Lemma GarbageGridH : ∀ n holes w, H (GarbageGrid n holes w) = Z.of_nat n. Proof. reflexivity. Qed.
Lemma GarbageGridW : ∀ n holes w, W (GarbageGrid n holes w) = w. Proof. reflexivity. Qed.

Lemma FPCroppedMgBox : ∀ [s6'] s pl holes
  (H1 : HW (T6.mg s6') = HW InitialMainGrid)
  (H2 : YX (T6.mg s6') = YX InitialMainGrid),
    HW (FP.CroppedMg' s pl s6' holes) = HW (T6.mg s6')
  ∧ YX (FP.CroppedMg' s pl s6' holes) = YX (T6.mg s6').
Proof.
  intros.
  destruct AxiomsInitialMainGrid as (H3 & H4 & H5 & _ & _).
  assert (H6 : Y (T6.mg s6') = 0) by (unfold Y; rewrite H2, H5; reflexivity).
  assert (H7 : X (T6.mg s6') = 0) by (unfold X; rewrite H2, H5; reflexivity).
  assert (H8 : W (T6.mg s6') = W InitialMainGrid) by (unfold W at 1; rewrite H1; reflexivity).
  assert (H9 : H (T6.mg s6') = H InitialMainGrid) by (unfold H at 1; rewrite H1; reflexivity).
  set (remGarbage := snd (GenRemGarbage (garbage s pl) (T6.clearedLines s6') (T6.perfectClear s6'))).
  set (garbageGrid := GarbageGrid remGarbage holes (W InitialMainGrid)).
  set (shiftedMg := T6.mg s6' ⊕ (Z.of_nat remGarbage, 0)).
  set (mask := {| L := λ y (_ : ℤ), (Z.of_nat remGarbage ≤? y)%Z; HW := HW shiftedMg; YX := YX shiftedMg |}).
  set (contained := shiftedMg ∩ mask).
  set (Mg'' := garbageGrid ∪ contained).
  assert (ECropped : FP.CroppedMg' s pl s6' holes = Mg'' ∩ Full (T6.mg s6')) by reflexivity.
  rewrite ECropped.
  (* Each layer is resolved all the way down to Y/X/H/W (T6.mg s6') before
  moving to the next, and its own scaffolding hypotheses are cleared right
  after. *)
  assert (SY : Y shiftedMg = Y (T6.mg s6') + Z.of_nat remGarbage)
    by (unfold shiftedMg; rewrite GridTranslateY; reflexivity).
  assert (SX : X shiftedMg = X (T6.mg s6'))
    by (unfold shiftedMg; rewrite GridTranslateX; simpl; lia).
  assert (SH : H shiftedMg = H (T6.mg s6'))
    by (unfold shiftedMg; rewrite GridTranslateH; reflexivity).
  assert (SW : W shiftedMg = W (T6.mg s6'))
    by (unfold shiftedMg; rewrite GridTranslateW; reflexivity).
  assert (MY : Y mask = Y (T6.mg s6') + Z.of_nat remGarbage) by (rewrite <- SY; reflexivity).
  assert (MX : X mask = X (T6.mg s6')) by (rewrite <- SX; reflexivity).
  assert (MH : H mask = H (T6.mg s6')) by (rewrite <- SH; reflexivity).
  assert (MW : W mask = W (T6.mg s6')) by (rewrite <- SW; reflexivity).
  assert (CY : Y contained = Y (T6.mg s6') + Z.of_nat remGarbage)
    by (unfold contained; rewrite GridIntersectY, SY, MY; lia).
  assert (CX : X contained = X (T6.mg s6'))
    by (unfold contained; rewrite GridIntersectX, SX, MX; lia).
  assert (CH : H contained = H (T6.mg s6'))
    by (unfold contained; rewrite GridIntersectH, SY, MY, SH, MH; lia).
  assert (CW : W contained = W (T6.mg s6'))
    by (unfold contained; rewrite GridIntersectW, SX, MX, SW, MW; lia).
  clear SY SX SH SW MY MX MH MW.
  assert (GY : Y garbageGrid = 0) by (unfold garbageGrid; rewrite GarbageGridY; reflexivity).
  assert (GX : X garbageGrid = 0) by (unfold garbageGrid; rewrite GarbageGridX; reflexivity).
  assert (GH : H garbageGrid = Z.of_nat remGarbage) by (unfold garbageGrid; rewrite GarbageGridH; reflexivity).
  assert (GW : W garbageGrid = W InitialMainGrid) by (unfold garbageGrid; rewrite GarbageGridW; reflexivity).
  assert (UY : Y Mg'' = 0)
    by (unfold Mg''; rewrite GridUnionY, GY, CY; lia).
  assert (UX : X Mg'' = X (T6.mg s6'))
    by (unfold Mg''; rewrite GridUnionX, GX, CX; lia).
  assert (UH : H Mg'' = Z.of_nat remGarbage + H (T6.mg s6'))
    by (unfold Mg''; rewrite GridUnionH, GY, GH, CY, CH; lia).
  assert (UW : W Mg'' = W (T6.mg s6'))
    by (unfold Mg''; rewrite GridUnionW, GX, GW, CX, CW; lia).
  clear CY CX CH CW GY GX GH GW.
  split.
  - apply injective_projections.
    + change (H (Mg'' ∩ Full (T6.mg s6')) = H (T6.mg s6')).
      rewrite GridIntersectH, GridFullY, GridFullH, UY, UH; lia.
    + change (W (Mg'' ∩ Full (T6.mg s6')) = W (T6.mg s6')).
      rewrite GridIntersectW, GridFullX, GridFullW, UX, UW; lia.
  - apply injective_projections.
    + change (Y (Mg'' ∩ Full (T6.mg s6')) = Y (T6.mg s6')).
      rewrite GridIntersectY, GridFullY, UY; lia.
    + change (X (Mg'' ∩ Full (T6.mg s6')) = X (T6.mg s6')).
      rewrite GridIntersectX, GridFullX, UX; lia.
Qed.

(****************************************)
(* GyEqShadowY holds by construction, thanks to the NewMainGridGameoverState
patch (T5.UpdateShadowY instead of T5.UnchangedT5Part). *)
Lemma NewMainGridGameoverStateGyEqShadowY : ∀ mg gmover s6,
  T6.gy (NewMainGridGameoverState mg gmover s6)
  = T5.ShadowY (T5.s4 (NewMainGridGameoverState mg gmover s6)).
Proof.
  intros; unfold T6.gy, T5.gy, NewMainGridGameoverState, T5.UpdateShadowY; reflexivity.
Qed.

(* Everything CorrectWithoutGameover asks for above the T1 mg/gameover level
(d, hold, swapped, level, totalClearedLines) is untouched by
NewMainGridGameoverState (except that GameoverImplyNotSwapped's antecedent
is the new gameover', so it can't reuse s6''s own instance of that conjunct);
instead `swapped` being unconditionally false after any fix makes its
conclusion trivial regardless of the antecedent. *)
Lemma NewMainGridGameoverStateOtherComponents : ∀ [s pl1 s6'] holes bagNew HbagNew
  (Hc6' : T6.CorrectWithoutGameover s6')
  (H6 : T6.FixPiece bagNew HbagNew (s6 s pl1) = Some s6'),
    T4.CorrectD (T4.d (T5.s4 (NewMainGridGameoverState
        (FP.CroppedMg' s pl1 s6' holes) (FP.Gameover' s pl1 s6' holes) s6')))
  ∧ T3.SwappedImplyHoldSome (T4.s3 (T5.s4 (NewMainGridGameoverState
        (FP.CroppedMg' s pl1 s6' holes) (FP.Gameover' s pl1 s6' holes) s6')))
  ∧ T3.GameoverImplyNotSwapped (T4.s3 (T5.s4 (NewMainGridGameoverState
        (FP.CroppedMg' s pl1 s6' holes) (FP.Gameover' s pl1 s6' holes) s6')))
  ∧ T2.LevelCorrect (T3.s2 (T4.s3 (T5.s4 (NewMainGridGameoverState
        (FP.CroppedMg' s pl1 s6' holes) (FP.Gameover' s pl1 s6' holes) s6')))).
Proof.
  intros.
  assert (Hrest : T4.CorrectD (T4.d (T5.s4 s6'))
                ∧ T3.SwappedImplyHoldSome (T4.s3 (T5.s4 s6'))
                ∧ T2.LevelCorrect (T3.s2 (T4.s3 (T5.s4 s6'))))
    by now unfold T6.CorrectWithoutGameover, T5.CorrectWithoutGameover,
      T4.CorrectWithoutGameover, T3.CorrectWithoutGameover,
      T2.CorrectWithoutGameover in Hc6'; tauto.
  destruct Hrest as (HD & HSw & HLvl).
  assert (Eswfalse : T3.swapped (T4.s3 (T5.s4 s6')) = false) by exact (T5P.FixPieceSwappedFalse H6).
  assert (Ed : T4.d (T5.s4 (NewMainGridGameoverState
                  (FP.CroppedMg' s pl1 s6' holes) (FP.Gameover' s pl1 s6' holes) s6'))
             = T4.d (T5.s4 s6')) by reflexivity.
  assert (Eswapped : T3.swapped (T4.s3 (T5.s4 (NewMainGridGameoverState
                        (FP.CroppedMg' s pl1 s6' holes) (FP.Gameover' s pl1 s6' holes) s6')))
                    = T3.swapped (T4.s3 (T5.s4 s6'))) by reflexivity.
  assert (Ehold : T3.hold (T4.s3 (T5.s4 (NewMainGridGameoverState
                        (FP.CroppedMg' s pl1 s6' holes) (FP.Gameover' s pl1 s6' holes) s6')))
                    = T3.hold (T4.s3 (T5.s4 s6'))) by reflexivity.
  assert (Elvl : T2.level (T3.s2 (T4.s3 (T5.s4 (NewMainGridGameoverState
                    (FP.CroppedMg' s pl1 s6' holes) (FP.Gameover' s pl1 s6' holes) s6'))))
              = T2.level (T3.s2 (T4.s3 (T5.s4 s6')))) by reflexivity.
  assert (Etcl : T2.totalClearedLines (T3.s2 (T4.s3 (T5.s4 (NewMainGridGameoverState
                    (FP.CroppedMg' s pl1 s6' holes) (FP.Gameover' s pl1 s6' holes) s6'))))
              = T2.totalClearedLines (T3.s2 (T4.s3 (T5.s4 s6')))) by reflexivity.
  refine (conj _ (conj _ (conj _ _))).
  - rewrite Ed; exact HD.
  - unfold T3.SwappedImplyHoldSome; rewrite Eswapped, Ehold; exact HSw.
  - unfold T3.GameoverImplyNotSwapped; intro; rewrite Eswapped; exact Eswfalse.
  - unfold T2.LevelCorrect; rewrite Elvl, Etcl; exact HLvl.
Qed.

Lemma NewMainGridGameoverStateTypeOK : ∀ [s pl1 holes s6']
  (Hc6' : T6.CorrectWithoutGameover s6'),
  T1.TypeOK (T2.s1 (T3.s2 (T4.s3 (T5.s4 (NewMainGridGameoverState
      (FP.CroppedMg' s pl1 s6' holes) (FP.Gameover' s pl1 s6' holes) s6'))))).
Proof.
  intros.
  assert (HT1 : T1.TypeOK (T2.s1 (T3.s2 (T4.s3 (T5.s4 s6')))))
    by now unfold T6.CorrectWithoutGameover, T5.CorrectWithoutGameover,
      T4.CorrectWithoutGameover, T3.CorrectWithoutGameover,
      T2.CorrectWithoutGameover, T1.CorrectWithoutGameover in Hc6'; tauto.
  destruct HT1 as (EHW & EYX & Epr).
  destruct (FPCroppedMgBox s pl1 holes EHW EYX) as (EHW' & EYX').
  assert (Emg : T1.mg (T2.s1 (T3.s2 (T4.s3 (T5.s4 (NewMainGridGameoverState
                  (FP.CroppedMg' s pl1 s6' holes) (FP.Gameover' s pl1 s6' holes) s6')))))
              = FP.CroppedMg' s pl1 s6' holes) by reflexivity.
  assert (Epr' : T1.pr (T2.s1 (T3.s2 (T4.s3 (T5.s4 (NewMainGridGameoverState
                  (FP.CroppedMg' s pl1 s6' holes) (FP.Gameover' s pl1 s6' holes) s6')))))
              = T1.pr (T2.s1 (T3.s2 (T4.s3 (T5.s4 s6'))))) by reflexivity.
  unfold T1.TypeOK; rewrite Emg, Epr'.
  split; [rewrite EHW'; exact EHW | split; [rewrite EYX'; exact EYX | exact Epr]].
Qed.

(* The fresh piece from FixPiece always spawns in the forbidden zone, so it's
inside any grid sharing the box (NewPieceInsideBounds, unconditional) and free
of whatever content that grid has, wherever the forbidden zone itself is free
(NewPieceFree, needed only when gameover' = false, i.e. exactly when
PieceOnFreeBlocks isn't vacuous). *)
Lemma NewMainGridGameoverStatePieceInvariants : ∀ [s pl1 s6'] holes bagNew HbagNew
  (Hc6' : T6.CorrectWithoutGameover s6')
  (H6 : T6.FixPiece bagNew HbagNew (s6 s pl1) = Some s6'),
    T1.PieceOccupiedInsideBounds (T2.s1 (T3.s2 (T4.s3 (T5.s4 (NewMainGridGameoverState
        (FP.CroppedMg' s pl1 s6' holes) (FP.Gameover' s pl1 s6' holes) s6')))))
  ∧ T1.PieceOnFreeBlocks (T2.s1 (T3.s2 (T4.s3 (T5.s4 (NewMainGridGameoverState
        (FP.CroppedMg' s pl1 s6' holes) (FP.Gameover' s pl1 s6' holes) s6')))))
.
Proof.
  intros.
  set (croppedMg' := FP.CroppedMg' s pl1 s6' holes).
  set (gameover' := FP.Gameover' s pl1 s6' holes).
  destruct (T5P.FixPieceFreshPiece H6) as [pNew (Ep & Epyx & Epr)].
  assert (HT1 : T1.TypeOK (T2.s1 (T3.s2 (T4.s3 (T5.s4 s6')))))
    by now unfold T6.CorrectWithoutGameover, T5.CorrectWithoutGameover,
      T4.CorrectWithoutGameover, T3.CorrectWithoutGameover,
      T2.CorrectWithoutGameover, T1.CorrectWithoutGameover in Hc6'; tauto.
  destruct HT1 as (EHW & EYX & _).
  destruct (FPCroppedMgBox s pl1 holes EHW EYX) as (EHW' & EYX').
  assert (Emg : T1.mg (T2.s1 (T3.s2 (T4.s3 (T5.s4
                  (NewMainGridGameoverState croppedMg' gameover' s6')))))
              = croppedMg') by reflexivity.
  assert (Ep' : T1.p (T2.s1 (T3.s2 (T4.s3 (T5.s4
                  (NewMainGridGameoverState croppedMg' gameover' s6')))))
              = pNew) by (rewrite <- Ep; reflexivity).
  assert (Epyx' : T1.pyx (T2.s1 (T3.s2 (T4.s3 (T5.s4
                  (NewMainGridGameoverState croppedMg' gameover' s6')))))
              = T1.InitialYX pNew) by (rewrite <- Epyx; reflexivity).
  assert (Epr' : T1.pr (T2.s1 (T3.s2 (T4.s3 (T5.s4
                  (NewMainGridGameoverState croppedMg' gameover' s6')))))
              = 0) by (rewrite <- Epr; reflexivity).
  assert (Ego : T1.gameover (T2.s1 (T3.s2 (T4.s3 (T5.s4
                  (NewMainGridGameoverState croppedMg' gameover' s6')))))
              = gameover') by reflexivity.
  split.
  - unfold T1.PieceOccupiedInsideBounds, T1.PieceGrid.
    rewrite Ep', Epr', Epyx', Emg.
    change (T1.RotGrid pNew 0 ⊕ T1.InitialYX pNew) with (T1P.NewPieceGrid pNew).
    apply T1P.NewPieceInsideBounds; unfold croppedMg';
      [rewrite EHW'; exact EHW | rewrite EYX'; exact EYX].
  - unfold T1.PieceOnFreeBlocks, T1.PieceGrid.
    rewrite Ego; intro Hgo.
    assert (Hforbidden : ForbiddenGrid ∩ croppedMg' ⊆ ∅ = true). {
      unfold gameover', FP.Gameover' in Hgo.
      apply Bool.orb_false_iff in Hgo as [_ Hgo3].
      apply Bool.negb_false_iff; exact Hgo3.
    }
    rewrite Ep', Epr', Epyx', Emg.
    change (T1.RotGrid pNew 0 ⊕ T1.InitialYX pNew) with (T1P.NewPieceGrid pNew).
    apply T1P.NewPieceFree; exact Hforbidden.
Qed.

Lemma GridUnionL : ∀ g1 g2 y x, L (g1 ∪ g2) y x = L g1 y x || L g2 y x.
Proof. reflexivity. Qed.

Lemma GridIntersectL : ∀ g1 g2 y x, L (g1 ∩ g2) y x = L g1 y x && L g2 y x.
Proof. reflexivity. Qed.

Lemma GridTranslateL : ∀ g dy dx y x, L (g ⊕ (dy, dx)) y x = L g (y - dy) (x - dx).
Proof. reflexivity. Qed.

Lemma GridFullL : ∀ g y x, L (Full g) y x = true.
Proof. reflexivity. Qed.

Lemma GarbageGridL : ∀ (n : ℕ) (holes : ℤ → ℕ) (w y x : ℤ),
  L (GarbageGrid n holes w) y x
  = (0 ≤? y <? Z.of_nat n) && (0 ≤? x <? w) && negb (x =? Z.of_nat (holes y)).
Proof. reflexivity. Qed.

Lemma NewMainGridGameoverStateNoFullLine : ∀ [s6' holes] s pl1
  (Hc6' : T6.CorrectWithoutGameover s6') (Hholes : ValidHoles holes),
  T1.NoFullLine (T2.s1 (T3.s2 (T4.s3 (T5.s4 (NewMainGridGameoverState
      (FP.CroppedMg' s pl1 s6' holes) (FP.Gameover' s pl1 s6' holes) s6'))))).
Proof.
  intros.
  assert (HT1 : T1.CorrectWithoutGameover (T2.s1 (T3.s2 (T4.s3 (T5.s4 s6')))))
    by now unfold T6.CorrectWithoutGameover, T5.CorrectWithoutGameover,
      T4.CorrectWithoutGameover, T3.CorrectWithoutGameover, T2.CorrectWithoutGameover
      in Hc6'; tauto.
  destruct HT1 as (HTO & _ & _ & HNFL6').
  destruct HTO as (H1box & H2box & _).
  destruct AxiomsInitialMainGrid as (H3 & H4 & H5 & _ & _).
  assert (H6 : Y (T6.mg s6') = 0)
    by (unfold Y, T6.mg, T5.mg, T4.mg; rewrite H2box, H5; reflexivity).
  assert (H7 : X (T6.mg s6') = 0)
    by (unfold X, T6.mg, T5.mg, T4.mg; rewrite H2box, H5; reflexivity).
  assert (H8 : W (T6.mg s6') = W InitialMainGrid)
    by (unfold W at 1, T6.mg, T5.mg, T4.mg; rewrite H1box; reflexivity).
  assert (H9 : H (T6.mg s6') = H InitialMainGrid)
    by (unfold H at 1, T6.mg, T5.mg, T4.mg; rewrite H1box; reflexivity).
  set (remGarbage := snd (GenRemGarbage (garbage s pl1) (T6.clearedLines s6') (T6.perfectClear s6'))).
  set (garbageGrid := GarbageGrid remGarbage holes (W InitialMainGrid)).
  set (shiftedMg := T6.mg s6' ⊕ (Z.of_nat remGarbage, 0)).
  set (mask := {| L := λ y (_ : ℤ), (Z.of_nat remGarbage ≤? y)%Z; HW := HW shiftedMg; YX := YX shiftedMg |}).
  set (contained := shiftedMg ∩ mask).
  set (Mg'' := garbageGrid ∪ contained).
  assert (ECropped : FP.CroppedMg' s pl1 s6' holes = Mg'' ∩ Full (T6.mg s6')) by reflexivity.
  assert (SY : Y shiftedMg = Y (T6.mg s6') + Z.of_nat remGarbage)
    by (unfold shiftedMg; rewrite GridTranslateY; reflexivity).
  assert (SX : X shiftedMg = X (T6.mg s6'))
    by (unfold shiftedMg; rewrite GridTranslateX; simpl; lia).
  assert (SH : H shiftedMg = H (T6.mg s6'))
    by (unfold shiftedMg; rewrite GridTranslateH; reflexivity).
  assert (SW : W shiftedMg = W (T6.mg s6'))
    by (unfold shiftedMg; rewrite GridTranslateW; reflexivity).
  assert (MY : Y mask = Y (T6.mg s6') + Z.of_nat remGarbage) by (rewrite <- SY; reflexivity).
  assert (MX : X mask = X (T6.mg s6')) by (rewrite <- SX; reflexivity).
  assert (MH : H mask = H (T6.mg s6')) by (rewrite <- SH; reflexivity).
  assert (MW : W mask = W (T6.mg s6')) by (rewrite <- SW; reflexivity).
  assert (CY : Y contained = Y (T6.mg s6') + Z.of_nat remGarbage)
    by (unfold contained; rewrite GridIntersectY, SY, MY; lia).
  assert (CX : X contained = X (T6.mg s6'))
    by (unfold contained; rewrite GridIntersectX, SX, MX; lia).
  assert (CH : H contained = H (T6.mg s6'))
    by (unfold contained; rewrite GridIntersectH, SY, MY, SH, MH; lia).
  assert (CW : W contained = W (T6.mg s6'))
    by (unfold contained; rewrite GridIntersectW, SX, MX, SW, MW; lia).
  assert (GY : Y garbageGrid = 0) by (unfold garbageGrid; rewrite GarbageGridY; reflexivity).
  assert (GX : X garbageGrid = 0) by (unfold garbageGrid; rewrite GarbageGridX; reflexivity).
  assert (GH : H garbageGrid = Z.of_nat remGarbage) by (unfold garbageGrid; rewrite GarbageGridH; reflexivity).
  assert (GW : W garbageGrid = W InitialMainGrid) by (unfold garbageGrid; rewrite GarbageGridW; reflexivity).
  assert (UY : Y Mg'' = 0) by (unfold Mg''; rewrite GridUnionY, GY, CY; lia).
  assert (UX : X Mg'' = X (T6.mg s6')) by (unfold Mg''; rewrite GridUnionX, GX, CX; lia).
  assert (UH : H Mg'' = Z.of_nat remGarbage + H (T6.mg s6'))
    by (unfold Mg''; rewrite GridUnionH, GY, GH, CY, CH; lia).
  assert (UW : W Mg'' = W (T6.mg s6')) by (unfold Mg''; rewrite GridUnionW, GX, GW, CX, CW; lia).
  assert (CropY : Y (FP.CroppedMg' s pl1 s6' holes) = 0)
    by (rewrite ECropped, GridIntersectY, GridFullY, UY; lia).
  assert (CropH : H (FP.CroppedMg' s pl1 s6' holes) = H (T6.mg s6'))
    by (rewrite ECropped, GridIntersectH, GridFullY, GridFullH, UY, UH; lia).
  assert (CropX : X (FP.CroppedMg' s pl1 s6' holes) = 0)
    by (rewrite ECropped, GridIntersectX, GridFullX, UX; lia).
  assert (CropW : W (FP.CroppedMg' s pl1 s6' holes) = W (T6.mg s6'))
    by (rewrite ECropped, GridIntersectW, GridFullX, GridFullW, UX, UW; lia).
  assert (Emg1 : T1.mg (T2.s1 (T3.s2 (T4.s3 (T5.s4 (NewMainGridGameoverState
                    (FP.CroppedMg' s pl1 s6' holes) (FP.Gameover' s pl1 s6' holes) s6')))))
              = FP.CroppedMg' s pl1 s6' holes) by reflexivity.
  unfold T1.NoFullLine, T1.HasFullLine.
  rewrite Emg1.
  intros (y & Hrange & HFull).
  rewrite CropY, CropH in Hrange.
  unfold T1.IsFullLine in HFull.
  assert (HFull' : ∀ x, 0 ≤ x < W (T6.mg s6') → L (FP.CroppedMg' s pl1 s6' holes) y x = true). {
    intros x Hx; apply HFull; rewrite CropX, CropW; lia.
  }
  clear HFull.
  assert (HLcrop : ∀ x, L (FP.CroppedMg' s pl1 s6' holes) y x = L Mg'' y x). {
    intro x; rewrite ECropped, GridIntersectL, GridFullL, Bool.andb_true_r; reflexivity.
  }
  destruct (Z_lt_ge_dec y (Z.of_nat remGarbage)) as [Hlt | Hge].
  - (* garbage row: the hole column is a counterexample *)
    assert (HxRange : 0 ≤ Z.of_nat (holes y) < W (T6.mg s6'))
      by (rewrite H8; exact (Hholes y)).
    specialize (HFull' (Z.of_nat (holes y)) HxRange).
    rewrite HLcrop in HFull'.
    unfold Mg'' in HFull'; rewrite GridUnionL in HFull'.
    assert (Hg0 : L garbageGrid y (Z.of_nat (holes y)) = false). {
      unfold garbageGrid; rewrite GarbageGridL.
      assert (Hneg : negb (Z.of_nat (holes y) =? Z.of_nat (holes y)) = false)
        by (rewrite Z.eqb_refl; reflexivity).
      rewrite Hneg, Bool.andb_false_r; reflexivity.
    }
    assert (Hc0 : L contained y (Z.of_nat (holes y)) = false). {
      unfold contained; rewrite GridIntersectL.
      assert (Hm0 : L mask y (Z.of_nat (holes y)) = false)
        by (unfold mask; simpl; apply Z.leb_gt; lia).
      rewrite Hm0, Bool.andb_false_r; reflexivity.
    }
    rewrite Hg0, Hc0 in HFull'; discriminate HFull'.
  - (* shifted-content row: use s6''s own NoFullLine at row y - remGarbage *)
    apply HNFL6'.
    exists (y - Z.of_nat remGarbage).
    split.
    + unfold T6.mg, T5.mg, T4.mg in H6, Hrange. rewrite H6. lia.
    + unfold T1.IsFullLine.
      intros x0 Hx0.
      unfold T6.mg, T5.mg, T4.mg in H7. rewrite H7 in Hx0.
      assert (Hx0' : 0 ≤ x0 < W (T6.mg s6')) by (unfold T6.mg, T5.mg, T4.mg; lia).
      specialize (HFull' x0 Hx0').
      rewrite HLcrop in HFull'.
      unfold Mg'' in HFull'; rewrite GridUnionL in HFull'.
      assert (Hg0 : L garbageGrid y x0 = false). {
        unfold garbageGrid; rewrite GarbageGridL.
        assert (Hyge : (y <? Z.of_nat remGarbage) = false) by (apply Z.ltb_ge; lia).
        rewrite Hyge, Bool.andb_false_r; reflexivity.
      }
      assert (Hc0 : L contained y x0 = L (T6.mg s6') (y - Z.of_nat remGarbage) x0). {
        unfold contained; rewrite GridIntersectL.
        assert (Hmtrue : L mask y x0 = true)
          by (unfold mask; simpl; apply Z.leb_le; lia).
        rewrite Hmtrue, Bool.andb_true_r.
        unfold shiftedMg; rewrite GridTranslateL.
        f_equal; lia.
      }
      rewrite Hg0, Bool.orb_false_l in HFull'.
      rewrite Hc0 in HFull'.
      exact HFull'.
Qed.

Lemma NewMainGridGameoverStateLowestShadowY : ∀ [s pl1 s6'] holes bagNew HbagNew
  (Hholes : ValidHoles holes)
  (Hc6' : T6.CorrectWithoutGameover s6')
  (H6 : T6.FixPiece bagNew HbagNew (s6 s pl1) = Some s6'),
  T5.LowestShadowY (NewMainGridGameoverState
      (FP.CroppedMg' s pl1 s6' holes) (FP.Gameover' s pl1 s6' holes) s6').
Proof.
  intros.
  set (croppedMg' := FP.CroppedMg' s pl1 s6' holes).
  set (gameover' := FP.Gameover' s pl1 s6' holes).
  unfold T5.LowestShadowY.
  intro Hgo.
  pose proof (@NewMainGridGameoverStateTypeOK s pl1 holes s6' Hc6') as HTO.
  destruct (NewMainGridGameoverStatePieceInvariants holes bagNew HbagNew Hc6' H6) as (HPoib & HPofb).
  destruct (NewMainGridGameoverStateOtherComponents holes bagNew HbagNew Hc6' H6)
    as (HD & HSw & HGov & HLvl).
  assert (HNFL := NewMainGridGameoverStateNoFullLine s pl1 Hc6' Hholes).
  assert (Hc4New : T4.CorrectWithoutGameover
                      (T5.s4 (NewMainGridGameoverState croppedMg' gameover' s6'))). {
    unfold T4.CorrectWithoutGameover, T3.CorrectWithoutGameover, T2.CorrectWithoutGameover,
      T1.CorrectWithoutGameover.
    exact (conj
      (conj
        (conj
          (conj HTO (conj HPoib (conj HPofb HNFL)))
          HLvl)
        (conj HSw HGov))
      HD).
  }
  assert (Hgo4 : T4.gameover (T5.s4 (NewMainGridGameoverState croppedMg' gameover' s6')) = false)
    by exact Hgo.
  destruct (T5P.ShadowYSpecWithoutGameover
              (T5.s4 (NewMainGridGameoverState croppedMg' gameover' s6')) Hc4New Hgo4)
    as (Hle & HVy & HVy1 & Hall).
  assert (Egy : T5.gy (NewMainGridGameoverState croppedMg' gameover' s6')
              = T5.ShadowY (T5.s4 (NewMainGridGameoverState croppedMg' gameover' s6')))
    by exact (NewMainGridGameoverStateGyEqShadowY croppedMg' gameover' s6').
  refine (conj _ (conj _ _)).
  - rewrite Egy; exact Hle.
  - rewrite Egy; exact (conj HVy HVy1).
  - intros y Hy1 Hy2.
    rewrite Egy.
    unfold T5.ValidPieceCannotGoDown in Hy2; destruct Hy2 as (Hy2a & Hy2b).
    exact (Hall y Hy1 Hy2a Hy2b).
Qed.
(****************************************)

Lemma FixPieceS6CorrectSingle : ∀ [s s' pl1 bagNew HbagNew s6']
  (H1 : S6Correct s)
  (H6 : T6.FixPiece bagNew HbagNew (s6 s pl1) = Some s6')
  (Hs6 : s6 s' = λ pl2, if (pl2 =? pl1)%player then s6' else s6 s pl2),
  S6Correct s'.
Proof.
  intros; unfold S6Correct; intro pl0.
  destruct (PlayerEqb pl0 pl1) eqn: Heq.
  - apply PlayerEqbEq1 in Heq; subst pl0.
    assert (Hs6pl1 : s6 s' pl1 = s6') by (rewrite Hs6, (PlayerEqbReflexive pl1); reflexivity).
    split.
    + rewrite Hs6pl1.
      exact (T5P.FixPieceCorrectWithoutGameover (proj1 (H1 pl1)) H6).
    + unfold Gameover, mg, gameover; rewrite Hs6pl1.
      intro Hforbidden.
      rewrite <- Hforbidden.
      exact (T5P.FixPieceGameoverEq H6).
  - assert (Hs6pl0 : s6 s' pl0 = s6 s pl0) by (rewrite Hs6, Heq; reflexivity).
    split.
    + rewrite Hs6pl0; exact (proj1 (H1 pl0)).
    + unfold Gameover, mg, gameover; rewrite Hs6pl0; exact (proj2 (H1 pl0)).
Qed.

Lemma FixPieceS6CorrectMulti : ∀ [s s' pl1 bagNew HbagNew s6'] (holes : ℤ → ℕ)
  (Hholes : ValidHoles holes)
  (H1 : S6Correct s)
  (H6 : T6.FixPiece bagNew HbagNew (s6 s pl1) = Some s6')
  (Hs6 : s6 s' = λ pl2,
      if (pl2 =? pl1)%player then
        NewMainGridGameoverState (FP.CroppedMg' s pl1 s6' holes) (FP.Gameover' s pl1 s6' holes) s6'
      else
        s6 s pl2),
  S6Correct s'.
Proof.
  intros; unfold S6Correct; intro pl0.
  set (gameover' := FP.Gameover' s pl1 s6' holes) in Hs6.
  destruct (PlayerEqb pl0 pl1) eqn: Heq.
  - apply PlayerEqbEq1 in Heq; subst pl0.
    assert (Hs6pl1 : s6 s' pl1
        = NewMainGridGameoverState (FP.CroppedMg' s pl1 s6' holes) gameover' s6')
      by (rewrite Hs6, (PlayerEqbReflexive pl1); reflexivity).
    split.
    + rewrite Hs6pl1.
      pose proof (proj1 (H1 pl1)) as Hc6'.
      pose proof (T5P.FixPieceCorrectWithoutGameover Hc6' H6) as Hc6'cwg.
      destruct (NewMainGridGameoverStateOtherComponents holes bagNew HbagNew Hc6'cwg H6)
        as (HD & HSw & HGov & HLvl).
      destruct (NewMainGridGameoverStatePieceInvariants holes bagNew HbagNew Hc6'cwg H6)
        as (HPoib & HPofb).
      exact (conj
        (conj
          (conj
            (conj
              (conj (NewMainGridGameoverStateTypeOK Hc6'cwg)
                    (conj HPoib
                          (conj HPofb
                                (NewMainGridGameoverStateNoFullLine s pl1 Hc6'cwg Hholes))))
              HLvl)
            (conj HSw HGov))
          HD)
          (conj (NewMainGridGameoverStateLowestShadowY holes bagNew HbagNew Hholes Hc6'cwg H6)
              (NewMainGridGameoverStateGyEqShadowY
                 (FP.CroppedMg' s pl1 s6' holes) gameover' s6'))).
    + unfold Gameover, mg, gameover; rewrite Hs6pl1.
      assert (EmgNew : T6.mg (NewMainGridGameoverState
                          (FP.CroppedMg' s pl1 s6' holes) gameover' s6')
                      = FP.CroppedMg' s pl1 s6' holes)
        by (unfold T6.mg, NewMainGridGameoverState; reflexivity).
      rewrite EmgNew, (NewMainGridGameoverStateGameover
                         (FP.CroppedMg' s pl1 s6' holes) gameover' s6').
      intro Hforbidden.
      unfold gameover', FP.Gameover'.
      apply orb_true_iff; right; exact Hforbidden.
  - assert (Hs6pl0 : s6 s' pl0 = s6 s pl0) by (rewrite Hs6, Heq; reflexivity).
    split.
    + rewrite Hs6pl0; exact (proj1 (H1 pl0)).
    + unfold Gameover, mg, gameover; rewrite Hs6pl0; exact (proj2 (H1 pl0)).
Qed. (* modulo NewMainGridGameoverStateNoFullLine / NewMainGridGameoverStateLowestShadowY *)

Lemma FixPieceS6Correct : ∀ [s s' pl1 holes Hholes bagNew HbagNew]
  (H1 : S6Correct s)
  (H3 : FixPiece pl1 holes Hholes bagNew HbagNew s = Some s'),
  S6Correct s'.
Proof.
  intros.
  unfold FixPiece in H3.
  apply IfSome, T5P.OptionMapSome in H3.
  destruct H3 as [s6' [H6 H7]]; cbv beta in H7.
  destruct ((PlayerCount =? 1)%nat) eqn: HPC.
  - (* Case PlayerCount = 1 *)
    apply (FixPieceS6CorrectSingle H1 H6).
    rewrite <- H7; unfold UpdatePlayer; reflexivity.
  - (* Case PlayerCount > 1 *)
    apply (FixPieceS6CorrectMulti holes Hholes H1 H6).
    rewrite <- H7; reflexivity.
Qed.

Lemma FallStepS6Correct : ∀ [s s' pl1 holes Hholes bagNew HbagNew]
  (H1 : S6Correct s)
  (H3 : FallStep pl1 holes Hholes bagNew HbagNew s = Some s'),
  S6Correct s'.
Proof.
  intros.
  unfold FallStep in H3.
  destruct (! WinnerMulti s pl1) eqn: L1; [| discriminate H3].
  destruct (MovePiece pl1 ((-1)%Z, 0%Z) s) as [s6' |] eqn: L2.
  + inject H3; unfold MovePiece in L2; rewrite <- H3.
    apply (MovePieceS6Correct H1 L2).
  + apply (FixPieceS6Correct H1 H3).
Qed.

Definition s1 (s6 : T6.State) : T1.State :=
  T2.s1 (T3.s2 (T4.s3 (T5.s4 (T6.s5 s6)))).

Lemma T6NewPieceYXStateSpec : ∀ [pyx s6 s6New]
  (H1 : s6New = T6.NewPieceYXState pyx s6),
    T6.mg s6 = T6.mg s6New
  ∧ T6.p s6 = T6.p s6New
  ∧ T6.pyx s6New = pyx
  ∧ T6.pr s6 = T6.pr s6New
  ∧ T6.gameover s6 = T6.gameover s6New
  ∧ T6.clearedLines s6 = T6.clearedLines s6New
  ∧ T6.score s6 = T6.score s6New
  ∧ T6.level s6 = T6.level s6New
  ∧ T6.combo s6 = T6.combo s6New
  ∧ T6.perfectClear s6 = T6.perfectClear s6New
  ∧ T6.totalClearedLines s6 = T6.totalClearedLines s6New
  ∧ T6.hold s6 = T6.hold s6New
  ∧ T6.swapped s6 = T6.swapped s6New
  ∧ T6.d s6 = T6.d s6New
  ∧ T6.gy s6 = T6.gy s6New.
Proof.
  intros.
  unfold T6.NewPieceYXState, T5.NewPieceYXState, T1.NewPieceYXState,
  T5.UnchangedT5Part, T4.UnchangedT4Part, T3.UnchangedT3Part, T2.UnchangedT2Part in H1.
  split_top; now rewrite H1.
Qed.

Lemma NewPieceYXStateS6CorrectWithoutGameover : ∀ [s6]
  (H1 : T6.CorrectWithoutGameover s6),
  T6.CorrectWithoutGameover (T6.NewPieceYXState (T6.gy s6, T6.px s6) s6).
Proof.
  intros.
  set (s4 := T5.s4 s6).
  set (s3 := T4.s3 s4).
  set (s2 := T3.s2 s3).
  set (s1 := T2.s1 s2).
  set (s6New := T6.NewPieceYXState (T6.gy s6, T6.px s6) s6).
  set (s4New := T5.s4 s6New).
  set (s3New := T4.s3 s4New).
  set (s2New := T3.s2 s3New).
  set (s1New := T2.s1 s2New).
  unfold T6.CorrectWithoutGameover, T5.CorrectWithoutGameover, T4.CorrectWithoutGameover,
    T3.CorrectWithoutGameover, T2.CorrectWithoutGameover, T1.CorrectWithoutGameover.
  #[local] Ltac ExtractFromCWG H :=
      unfold T6.CorrectWithoutGameover, T5.CorrectWithoutGameover,
      T4.CorrectWithoutGameover, T3.CorrectWithoutGameover, T2.CorrectWithoutGameover,
      T1.CorrectWithoutGameover in H; tauto.
  assert (L1 : T1.TypeOK s1New). {
    assert (L1_1 : T1.TypeOK s1) by now ExtractFromCWG H1.
    exact L1_1.
  }
  assert (L2 : T1.PieceOccupiedInsideBounds s1New). {
    assert (Hgy : T6.gy s6 = T5.ShadowY s4)
      by now unfold T6.CorrectWithoutGameover, T5.CorrectWithoutGameover in H1; tauto.
    assert (Emg41 : T4.mg s4 = T1.mg s1) by reflexivity.
    assert (Ep41  : T4.p  s4 = T1.p  s1) by reflexivity.
    assert (Epr41 : T4.pr s4 = T1.pr s1) by reflexivity.
    assert (Epx41 : T4.px s4 = T1.px s1) by reflexivity.
    assert (Epy41 : T4.py s4 = T1.py s1) by reflexivity.
    assert (Epx6  : T6.px s6 = T4.px s4) by reflexivity.
    assert (Emg1' : T1.mg s1New = T1.mg s1) by reflexivity.
    assert (Ep1'  : T1.p  s1New = T1.p  s1) by reflexivity.
    assert (Epr1' : T1.pr s1New = T1.pr s1) by reflexivity.
    assert (Epyx1' : T1.pyx s1New = (T6.gy s6, T6.px s6)) by reflexivity.
    destruct (T5P.ShadowYValidOrNoMove s4) as [Hno | Hval].
    - (* no movement: (gy s6, px s6) is exactly s6's own current position *)
      assert (Hpoib1 : T1.PieceOccupiedInsideBounds s1)
        by now unfold T6.CorrectWithoutGameover, T5.CorrectWithoutGameover,
          T4.CorrectWithoutGameover, T3.CorrectWithoutGameover,
          T2.CorrectWithoutGameover, T1.CorrectWithoutGameover in H1; tauto.
      assert (Epyx : T1.pyx s1New = T1.pyx s1). {
        rewrite Epyx1', Hgy, Hno, Epy41, Epx6, Epx41.
        unfold T1.py, T1.px.
        symmetry; apply surjective_pairing.
      }
      unfold T1.PieceOccupiedInsideBounds, T1.PieceGrid in Hpoib1 |- *.
      rewrite Emg1', Ep1', Epr1', Epyx.
      exact Hpoib1.
    - (* real descent: Valid was confirmed at (gy s6, px s6) *)
      rewrite Emg41, Ep41, Epr41, Epx41 in Hval.
      assert (Hvalid : T1.Valid (T1.mg s1New) (T1.p s1New) (T1.pyx s1New) (T1.pr s1New) = true). {
        rewrite Emg1', Ep1', Epr1', Epyx1', Hgy, Epx6, Epx41.
        exact Hval.
      }
      destruct (T1P.ValidPieceInvariants s1New Hvalid) as [Hpoib _].
      exact Hpoib.
  }
  assert (L3 : T1.PieceOnFreeBlocks s1New). {
    assert (Hgy : T6.gy s6 = T5.ShadowY s4)
      by now unfold T6.CorrectWithoutGameover, T5.CorrectWithoutGameover in H1; tauto.
    assert (Emg41 : T4.mg s4 = T1.mg s1) by reflexivity.
    assert (Ep41  : T4.p  s4 = T1.p  s1) by reflexivity.
    assert (Epr41 : T4.pr s4 = T1.pr s1) by reflexivity.
    assert (Epx41 : T4.px s4 = T1.px s1) by reflexivity.
    assert (Epy41 : T4.py s4 = T1.py s1) by reflexivity.
    assert (Epx6  : T6.px s6 = T4.px s4) by reflexivity.
    assert (Emg1' : T1.mg s1New = T1.mg s1) by reflexivity.
    assert (Ep1'  : T1.p  s1New = T1.p  s1) by reflexivity.
    assert (Epr1' : T1.pr s1New = T1.pr s1) by reflexivity.
    assert (Ego1' : T1.gameover s1New = T1.gameover s1) by reflexivity.
    assert (Epyx1' : T1.pyx s1New = (T6.gy s6, T6.px s6)) by reflexivity.
    destruct (T5P.ShadowYValidOrNoMove s4) as [Hno | Hval].
    - assert (Hpofb1 : T1.PieceOnFreeBlocks s1)
        by now unfold T6.CorrectWithoutGameover, T5.CorrectWithoutGameover,
          T4.CorrectWithoutGameover, T3.CorrectWithoutGameover,
          T2.CorrectWithoutGameover, T1.CorrectWithoutGameover in H1; tauto.
      assert (Epyx : T1.pyx s1New = T1.pyx s1). {
        rewrite Epyx1', Hgy, Hno, Epy41, Epx6, Epx41.
        unfold T1.py, T1.px.
        symmetry; apply surjective_pairing.
      }
      unfold T1.PieceOnFreeBlocks, T1.PieceGrid in Hpofb1 |- *.
      rewrite Emg1', Ep1', Epr1', Epyx, Ego1'.
      exact Hpofb1.
    - rewrite Emg41, Ep41, Epr41, Epx41 in Hval.
      assert (Hvalid : T1.Valid (T1.mg s1New) (T1.p s1New) (T1.pyx s1New) (T1.pr s1New) = true). {
        rewrite Emg1', Ep1', Epr1', Epyx1', Hgy, Epx6, Epx41.
        exact Hval.
      }
      destruct (T1P.ValidPieceInvariants s1New Hvalid) as [_ Hpofb].
      exact Hpofb.
  }
  assert (L4 : T1.NoFullLine s1New). {
    assert (L4_1 : T1.NoFullLine s1) by now ExtractFromCWG H1.
    exact L4_1.
  }
  assert (L5 : T2.LevelCorrect s2New). {
    assert (L5_1 : T2.LevelCorrect s2) by now ExtractFromCWG H1.
    exact L5_1.
  }
  assert (L6 : T3.SwappedImplyHoldSome s3New). {
    assert (L6_1 : T3.SwappedImplyHoldSome s3) by now ExtractFromCWG H1.
    exact L6_1.
  }
  assert (L7 : T3.GameoverImplyNotSwapped s3New). {
    assert (L7_1 : T3.GameoverImplyNotSwapped s3) by now ExtractFromCWG H1.
    exact L7_1.
  }
  assert (L8 : T4.CorrectD (T4.d s4New)). {
    assert (L8_1 : T4.CorrectD (T4.d s4)) by now ExtractFromCWG H1.
    exact L8_1.
  }
  assert (L9 : T5.LowestShadowY s6New). {
    unfold T5.LowestShadowY.
    intro Hgo.
    assert (Ego : T5.gameover s6New = T5.gameover s6) by reflexivity.
    rewrite Ego in Hgo.
    assert (HLow : T5.LowestShadowY s6)
      by now unfold T6.CorrectWithoutGameover, T5.CorrectWithoutGameover in H1; tauto.
    unfold T5.LowestShadowY in HLow; specialize (HLow Hgo).
    destruct HLow as (_ & HVgy & _).
    assert (Egy : T5.gy s6New = T5.gy s6) by reflexivity.
    assert (Epy : T5.py s6New = T5.gy s6) by reflexivity.
    assert (Emg : T5.mg s6New = T5.mg s6) by reflexivity.
    assert (Ep  : T5.p  s6New = T5.p  s6) by reflexivity.
    assert (Epr : T5.pr s6New = T5.pr s6) by reflexivity.
    assert (Epx : T5.px s6New = T5.px s6) by reflexivity.
    #[local] Ltac DischargeT1Valid HVgy Egy Emg Ep Epr Epx :=
      unfold T5.ValidPieceCannotGoDown in HVgy |- *;
      rewrite Egy, Emg, Ep, Epr, Epx;
      keep_only HVgy; tauto.
    repeat split;
      (rewrite Egy, Epy; lia) || (DischargeT1Valid HVgy Egy Emg Ep Epr Epx) ||
      (intros y Hy1 _; rewrite Epy in Hy1; rewrite Egy; exact Hy1).
  }
  assert (L10 : T5.GyEqShadowY s6New). {
    assert (L10_1 : T5.gy s6 = T5.gy s6New)
      by now ExtractFromCWG H1.
    assert (L10_2 : T5.ShadowY s4 = T5.ShadowY (T5.s4 s6New)). {
      assert (Hc4 : T4.CorrectWithoutGameover s4)
        by now unfold T6.CorrectWithoutGameover, T5.CorrectWithoutGameover in H1; tauto.
      assert (Emg : T4.mg (T5.s4 s6New) = T4.mg s4) by reflexivity.
      assert (Ep  : T4.p  (T5.s4 s6New) = T4.p  s4) by reflexivity.
      assert (Epr : T4.pr (T5.s4 s6New) = T4.pr s4) by reflexivity.
      assert (Epx : T4.px (T5.s4 s6New) = T4.px s4) by reflexivity.
      assert (Epy : T4.py (T5.s4 s6New) = T5.ShadowY s4). {
        assert (E1 : T4.py (T5.s4 s6New) = T6.gy s6) by reflexivity.
        assert (E2 : T6.gy s6 = T5.ShadowY s4) by now ExtractFromCWG H1.
        rewrite E1; exact E2.
      }
      symmetry; exact (T5P.ShadowYIdempotent s4 (T5.s4 s6New) Hc4 Emg Ep Epr Epx Epy).
    }
    assert (L10_3 : T5.gy s6 = T5.ShadowY s4)
      by now ExtractFromCWG H1.
    unfold T5.GyEqShadowY.
    rewrite <- L10_1, <- L10_2.
    exact L10_3.
  }
  repeat split_top; auto using L1, L2, L3, L4, L5, L6, L7, L8, L9, L10.
Qed.

Lemma NewPieceYXStateMgUnchanged : ∀ s pyxNew pl1 pl2,
  mg (NewPieceYXState pyxNew pl1 s) pl2 = mg s pl2.
Proof.
  intros; unfold gameover, NewPieceYXState, UnchangedT7Part,
  T6.NewPieceYXState, T5.NewPieceYXState, T1.NewPieceYXState,
  T5.UnchangedT5Part, T4.UnchangedT4Part, T3.UnchangedT3Part, T2.UnchangedT2Part,
  mg; simpl.
  destruct (PlayerEqb pl2 pl1) eqn: L1; [ | reflexivity].
  apply PlayerEqbEq1 in L1; now rewrite L1.
Qed.

Lemma NewPieceYXStateGameover : ∀ [s pl1] pl2
  (H1 : Gameover pl1 s),
  Gameover pl1 (NewPieceYXState (gy s pl2, px s pl2) pl2 s).
Proof.
  intros; unfold Gameover.
  rewrite NewPieceYXStateMgUnchanged, NewPieceYXStateGameoverUnchanged.
  exact H1.
Qed.

Lemma NewPieceYXStateS6Correct : ∀ [s] pl
  (H1 : S6Correct s),
  S6Correct (NewPieceYXState (gy s pl, px s pl) pl s).
Proof.
  unfold S6Correct.
  intros.
  set (sNew := NewPieceYXState (gy s pl, px s pl) pl s).
  split.
  - enough (T6.CorrectWithoutGameover (s6 sNew pl0)) by trivial.
    assert (L1 : T6.CorrectWithoutGameover (s6 s pl))
      by now pose proof (H1 pl); tauto.
      simpl; destruct ((pl0 =? pl)%player) eqn: L2.
      + exact (NewPieceYXStateS6CorrectWithoutGameover L1).
      + pose proof (H1 pl0); tauto.
  - enough (Gameover pl0 sNew) by trivial.
    assert (L1 : Gameover pl0 s) by now pose proof (H1 pl0); tauto.
    exact (NewPieceYXStateGameover pl L1).
Qed.

Lemma DropPieceS6Correct : ∀ [s s' pl1 holes Hholes bagNew HbagNew]
  (H1 : S6Correct s)
  (H3 : DropPiece pl1 holes Hholes bagNew HbagNew s = Some s'),
  S6Correct s'.
Proof.
  intros.
  set (sNew := NewPieceYXState (gy s pl1, px s pl1) pl1 s).
  assert (L1 : S6Correct sNew) by now exact (NewPieceYXStateS6Correct pl1 H1).
  unfold DropPiece in H3.
  exact (FixPieceS6Correct L1 H3).
Qed.

Lemma NextS6Correct : ∀ [pl1 e s s']
  (H1 : S6Correct s)
  (H3 : Next pl1 e s = Some s'),
  S6Correct s'.
Proof.
  intros.
  destruct e in H3; simpl in H3; (
    eapp MovePieceS6Correct || eapp RotatePieceS6Correct ||
    eapp FixPieceS6Correct || eapp FallStepS6Correct ||
    eapp HoldPieceS6Correct || eapp DropPieceS6Correct ||
    eapp RotateKickPieceS6Correct || eapp ReceiveMessageS6Correct ||
    eapp DisconnectPlayerS6Correct || eapp NoticeDisconnectionS6Correct ||
    eapp StutterS6Correct).
Qed.

Theorem SpecS6Correct :
   (∀ bags H, S6Correct (Init bags H))
 ∧ (∀ [pl e s s']
      (H1 : S6Correct s)
      (H2 : Next pl e s = Some s'),
      S6Correct s').
Proof.
  split; (eapp InitS6Correct || eapp NextS6Correct).
Qed.


(* ========================================================================= *)
(* Correct                                                                   *)
(* ========================================================================= *)

Lemma InitCorrect : ∀ bags H,
  Correct (Init bags H).
Proof.
  intros; unfold Correct, TargetNotSelf, TargetPlaying; split_top; (
    eapp InitS6Correct || eapp InitSelfViewAccurate || eapp InitViewSound ||
    eapp InitMessageSound || eapp InitNoSelfMessage || eapp InitLastMessagesGameoverDisconnect ||
    eapp InitTargetNotSelf || eapp InitTargetPlaying).
Qed.

Lemma NextCorrect : ∀ [pl1 e s s']
  (H1 : Correct s)
  (H2 : Next pl1 e s = Some s'),
  Correct s'.
Proof.
  intros.
  assert (L1 : ∀ [dyx], MovePiece pl1 dyx s = Some s' → Correct s')
    by now intros; split_top; sauto use:
      MovePieceS6Correct, MovePieceSelfViewAccurate, MovePieceViewSound,
      MovePieceMessageSound, MovePieceNoSelfMessage, MovePieceLastMessagesGameoverDisconnect,
      MovePieceTargetNotSelf, MovePieceTargetPlaying.
  assert (L2 : ∀ [cw], RotatePiece pl1 cw s = Some s' → Correct s')
    by now intros; split_top; sauto use:
      RotatePieceS6Correct, RotatePieceSelfViewAccurate, RotatePieceViewSound,
      RotatePieceMessageSound, RotatePieceNoSelfMessage, RotatePieceLastMessagesGameoverDisconnect,
      RotatePieceTargetNotSelf, RotatePieceTargetPlaying.
  assert (L3 : ∀ [holes Hholes bagNew HbagNew],
      FixPiece pl1 holes Hholes bagNew HbagNew s = Some s' → Correct s')
    by now intros; split_top; sauto use:
      FixPieceS6Correct, FixPieceSelfViewAccurate, FixPieceViewSound,
      FixPieceMessageSound, FixPieceNoSelfMessage, FixPieceLastMessagesGameoverDisconnect,
      FixPieceTargetNotSelf, FixPieceTargetPlaying.
  assert (L4 : ∀ [holes Hholes bagNew HbagNew],
      FallStep pl1 holes Hholes bagNew HbagNew s = Some s' → Correct s')
    by now intros; split_top; sauto use:
      FallStepS6Correct, FallStepSelfViewAccurate, FallStepViewSound,
      FallStepMessageSound, FallStepNoSelfMessage, FallStepLastMessagesGameoverDisconnect,
      FallStepTargetNotSelf, FallStepTargetPlaying.
  assert (L5 : ∀ [holes Hholes bagNew HbagNew],
      HoldPiece pl1 holes Hholes bagNew HbagNew s = Some s' → Correct s')
    by now intros; split_top; sauto use:
      HoldPieceS6Correct, HoldPieceSelfViewAccurate, HoldPieceViewSound, HoldPieceMessageSound,
      HoldPieceNoSelfMessage, HoldPieceLastMessagesGameoverDisconnect, HoldPieceTargetNotSelf,
      HoldPieceTargetPlaying.
  assert (L6 : ∀ [holes Hholes bagNew HbagNew],
      DropPiece pl1 holes Hholes bagNew HbagNew s = Some s' → Correct s')
    by now intros; split_top; sauto use:
      DropPieceS6Correct, DropPieceSelfViewAccurate, DropPieceViewSound,
      DropPieceMessageSound, DropPieceNoSelfMessage, DropPieceLastMessagesGameoverDisconnect,
      DropPieceTargetNotSelf, DropPieceTargetPlaying.
  assert (L7 : ∀ [cw], RotateKickPiece pl1 cw s = Some s' → Correct s')
    by now intros; split_top; sauto use:
      RotateKickPieceS6Correct, RotateKickPieceSelfViewAccurate, RotateKickPieceViewSound,
      RotateKickPieceMessageSound, RotateKickPieceNoSelfMessage, RotateKickPieceLastMessagesGameoverDisconnect,
      RotateKickPieceTargetNotSelf, RotateKickPieceTargetPlaying.
  assert (L8 : ∀ [pl2], ReceiveMessage pl1 pl2 s = Some s' → Correct s')
    by now intros; split_top; sauto use:
      ReceiveMessageS6Correct, ReceiveMessageSelfViewAccurate, ReceiveMessageViewSound,
      ReceiveMessageMessageSound, ReceiveMessageNoSelfMessage, ReceiveMessageLastMessagesGameoverDisconnect,
      ReceiveMessageTargetNotSelf, ReceiveMessageTargetPlaying.
  assert (L9 : DisconnectPlayer pl1 s = Some s' → Correct s')
    by now intros; split_top; sauto use:
      DisconnectPlayerS6Correct, DisconnectPlayerSelfViewAccurate, DisconnectPlayerViewSound,
      DisconnectPlayerMessageSound, DisconnectPlayerNoSelfMessage, DisconnectPlayerLastMessagesGameoverDisconnect,
      DisconnectPlayerTargetNotSelf, DisconnectPlayerTargetPlaying.
  assert (L10 : NoticeDisconnection pl1 s = Some s' → Correct s')
    by now intros; split_top; sauto use:
      NoticeDisconnectionS6Correct, NoticeDisconnectionSelfViewAccurate, NoticeDisconnectionViewSound,
      NoticeDisconnectionMessageSound, NoticeDisconnectionNoSelfMessage, NoticeDisconnectionLastMessagesGameoverDisconnect,
      NoticeDisconnectionTargetNotSelf, NoticeDisconnectionTargetPlaying.
  destruct e in H2; simpl in H2; sauto use: L1, L2, L3, L4, L5, L6, L7, L8, L9, L10.
Qed.

Theorem SpecCorrect :
   (∀ bags H, Correct (Init bags H))
 ∧ (∀ [pl e s s']
      (H1 : Correct s)
      (H2 : Next pl e s = Some s'),
      Correct s').
Proof.
  split; (eapp InitCorrect || eapp NextCorrect).
Qed.