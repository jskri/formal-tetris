From Tetris Require Import T7 Notations.
From Tetris Require T1 T6.
From Tetris Require T1Proofs T5Proofs T6Proofs.
Module T1P := T1Proofs.
Module T5P := T5Proofs.
Module T6P := T6Proofs.
Import (notations) T1.
Import T1(AxiomsInitialMainGrid, Grid, L, HW, H, W, YX, Y, X, InitialMainGrid,
  ForbiddenGrid, GridIntersect, GridUnion, GridTranslate).
From Stdlib Require Import Lia PeanoNat ZArith Bool List.
From Stdlib Require Import Logic.FunctionalExtensionality.
Import ListNotations.

#[local] Open Scope nat_scope.

(* Proof style: proofs do not depend on the order of conjuncts, disjuncts,
 * hypotheses, lemma premises or event constructors. Same rules as T6Proofs.v:
 * - a fact is taken out of a conjunction by stating it, e.g.
 *   [assert (F : fact) by (apply L in H; tauto)],
 * - a conjunction is proven by first stating all its conjuncts, then closing
 *   every branch with the same tactic (e.g. [split_top; assumption]),
 * - a lemma with several premises is applied with [eapp] or [apply ... in],
 *   not by passing hypotheses positionally,
 * - a disjunction is taken apart with [decompose], and every case is closed
 *   with the same tactic,
 * - a case analysis on an event closes every case with the same tactic.
 *
 * Every event is first reduced to one of the six ways a step can change the
 * state ([Step] below). Each invariant is then proven once for all of them:
 * [step_cases] writes the new state as an explicit record, [player_cases]
 * decides the player comparisons it contains, and one list of closing tactics
 * covers all the cases. *)

(* The T1 part of a T6 state. *)
Local Notation s1 s6 := (T2.s1 (T3.s2 (T4.s3 (T5.s4 s6)))).


(* ========================================================================= *)
(* Players                                                                   *)
(* ========================================================================= *)

Lemma PlayerEqbTrue : ∀ [pl1 pl2] (H1 : PlayerEqb pl1 pl2 = true), pl1 = pl2.
Proof. intros; apply PlayerEqbEq; exact H1. Qed.

Lemma PlayerEqbFalse : ∀ [pl1 pl2] (H1 : PlayerEqb pl1 pl2 = false), pl1 ≠ pl2.
Proof. intros pl1 pl2 H1 E; apply PlayerEqbEq in E; congruence. Qed.

Lemma PlayerNeqb : ∀ [pl1 pl2] (H1 : pl1 ≠ pl2), PlayerEqb pl1 pl2 = false.
Proof. intros; destruct (PlayerEqb pl1 pl2) eqn: E; [ apply PlayerEqbTrue in E | ]; congruence. Qed.

Lemma PlayerEqbRefl : ∀ pl, PlayerEqb pl pl = true.
Proof. intros; apply PlayerEqbEq; reflexivity. Qed.

(* Decides [PlayerEqb a b] everywhere: either a = b, substituted when one side
 * is a variable, or a ≠ b. *)
Ltac player_case a b :=
  let E := fresh "E" in
  destruct (PlayerEqb a b) eqn: E; try rewrite E in *;
  [ apply PlayerEqbTrue in E; first [ subst b | subst a | idtac ]
  | apply PlayerEqbFalse in E ];
  cbn [andb orb negb] in *.

(* Decides every player comparison [PlayerEqb a b] satisfying [cond a b]. *)
Ltac player_cases_if cond :=
  repeat first
  [ rewrite PlayerEqbRefl in *
  | match goal with
    | |- context [PlayerEqb ?a ?b] => cond a b; player_case a b
    | _ : context [PlayerEqb ?a ?b] |- _ => cond a b; player_case a b
    end ].

Ltac atomic t := first [ is_var t | is_const t ].

(* Comparisons between players named by a variable or a constant (Host). *)
Ltac player_cases := player_cases_if ltac:(fun a b => atomic a; atomic b).

Ltac all_player_cases := player_cases_if ltac:(fun a b => idtac).


(* ========================================================================= *)
(* Steps                                                                     *)
(*                                                                           *)
(* A step changes the state in one of six ways: the acting player's T6 state *)
(* alone (the piece events, and Fix in single-player mode), a multiplayer    *)
(* Fix, or one of the network events. Fall is a move or a fix, and Drop is a *)
(* fix after moving the piece to its shadow (see [NextStep]).                *)
(* ========================================================================= *)

(* The gameover invariant of a player, as weakened by T7 (see T7.Gameover). *)
Definition S6Gameover (s6 : T6.State) : Prop :=
  ForbiddenGrid ∩ T6.mg s6 ⊈ ∅ = true → T6.gameover s6 = true.

(* What the invariants need to know of a T6 step of the acting player:
 * gameover is monotone, and the player's part of S6Correct is preserved. *)
Definition S6Step (s6 s6' : T6.State) : Prop :=
    (T6.gameover s6 = true → T6.gameover s6' = true)
  ∧ (T6.CorrectWithoutGameover s6 → S6Gameover s6 →
       T6.CorrectWithoutGameover s6' ∧ S6Gameover s6').

(* A piece event keeps the main grid and gameover, hence S6Gameover. *)
Lemma S6StepKeep : ∀ [s6 s6']
  (Hgo : T6.gameover s6 = true → T6.gameover s6' = true)
  (Hc : T6.CorrectWithoutGameover s6 → S6Gameover s6 →
          T6.CorrectWithoutGameover s6'
        ∧ T6.mg s6' = T6.mg s6 ∧ T6.gameover s6' = T6.gameover s6),
  S6Step s6 s6'.
Proof.
  unfold S6Step, S6Gameover; intros; split_top; intros; [ auto | split_top; [ tauto | ] ].
  assert (E1 : T6.mg s6' = T6.mg s6) by tauto.
  assert (E2 : T6.gameover s6' = T6.gameover s6) by tauto.
  rewrite E1, E2; auto.
Qed.

Lemma MoveS6Step : ∀ [dyx s6 s6'] (Hn : T6.MovePiece dyx s6 = Some s6'), S6Step s6 s6'.
Proof.
  intros; apply S6StepKeep; intros.
  - erewrite T5P.MovePieceUnchangedGameover; eassumption.
  - assert (Hc' : T6.CorrectWithoutGameover s6') by eapp T5P.MovePieceCorrectWithoutGameover.
    apply T5P.MovePieceMgGameoverUnchanged in Hn; tauto.
Qed.

Lemma RotateS6Step : ∀ [cw s6 s6'] (Hn : T6.RotatePiece cw s6 = Some s6'), S6Step s6 s6'.
Proof.
  intros; apply S6StepKeep; intros.
  - erewrite T5P.RotatePieceUnchangedGameover; eassumption.
  - assert (Hc' : T6.CorrectWithoutGameover s6') by eapp T5P.RotatePieceCorrectWithoutGameover.
    apply T5P.RotatePieceMgGameoverUnchanged in Hn; tauto.
Qed.

Lemma HoldS6Step : ∀ [bagNew H s6 s6'] (Hn : T6.HoldPiece bagNew H s6 = Some s6'), S6Step s6 s6'.
Proof.
  intros; apply S6StepKeep; intros.
  - apply T5P.HoldPieceNotGameover in Hn; unfold T6.gameover in *; congruence.
  - assert (Hc' : T6.CorrectWithoutGameover s6') by eapp T5P.HoldPieceCorrectWithoutGameover.
    apply T5P.HoldPieceMgGameoverUnchanged in Hn; tauto.
Qed.

Lemma RotateKickS6Step : ∀ [cw s6 s6'] (Hn : T6.RotateKickPiece cw s6 = Some s6'), S6Step s6 s6'.
Proof.
  intros; apply S6StepKeep; intros.
  - apply T6P.RotateKickNotGameover in Hn; congruence.
  - assert (Hc' : T6.CorrectWithoutGameover s6') by eapp T6P.RotateKickPieceCorrectWithoutGameover.
    assert (E : T6.mg s6' = T6.mg s6 ∧ T6.gameover s6' = T6.gameover s6)
      by eapp T6P.RotateKickPieceMgGameoverUnchanged.
    tauto.
Qed.

(* A fix needs a game not over, and sets gameover exactly as T1 does. *)
Lemma FixS6Step : ∀ [bagNew H s6 s6'] (Hn : T6.FixPiece bagNew H s6 = Some s6'), S6Step s6 s6'.
Proof.
  unfold S6Step, S6Gameover; intros; split_top; intros.
  - apply T5P.FixPieceNotGameover in Hn; unfold T6.gameover in *; congruence.
  - assert (Hc' : T6.CorrectWithoutGameover s6') by eapp T5P.FixPieceCorrectWithoutGameover.
    assert (E : T6.gameover s6' = (ForbiddenGrid ∩ T6.mg s6' ⊈ ∅)) by eapp T5P.FixPieceGameoverEq.
    rewrite E; split_top; auto.
Qed.

Inductive Step (pl : Player) (s : State) : State → Prop :=
  | StepUpdate s6' (H6 : S6Step (s6 s pl) s6') : Step pl s (UpdatePlayer s pl s6')
  | StepFix holes Hholes bagNew HbagNew s'
      (Hm : (PlayerCount =? 1) = false)
      (Hn : FixPiece pl holes Hholes bagNew HbagNew s = Some s') : Step pl s s'
  | StepReceive from s' (Hn : ReceiveMessage pl from s = Some s') : Step pl s s'
  | StepDisconnect s' (Hn : DisconnectPlayer pl s = Some s') : Step pl s s'
  | StepNotice s' (Hn : NoticeDisconnection pl s = Some s') : Step pl s s'
  | StepStutter : Step pl s s.

Lemma GuardedUpdateStep : ∀ [A pl s s'] [f : A → option T6.State] [x : A]
  (H6 : ∀ s6', f x = Some s6' → S6Step (s6 s pl) s6')
  (Hn : (if ! WinnerMulti s pl then option_map (UpdatePlayer s pl) (f x) else None) = Some s'),
  Step pl s s'.
Proof.
  intros; destruct (! WinnerMulti s pl); [ | discriminate Hn ].
  destruct (f x) eqn: E; cbn [option_map] in Hn; [ inject Hn; subst | discriminate Hn ].
  constructor; auto.
Qed.

Lemma MovePieceStep : ∀ [pl dyx s s'] (Hn : MovePiece pl dyx s = Some s'), Step pl s s'.
Proof. intros; eapply GuardedUpdateStep; [ intros; eapp MoveS6Step | exact Hn ]. Qed.

Lemma RotatePieceStep : ∀ [pl cw s s'] (Hn : RotatePiece pl cw s = Some s'), Step pl s s'.
Proof. intros; eapply GuardedUpdateStep; [ intros; eapp RotateS6Step | exact Hn ]. Qed.

Lemma HoldPieceStep : ∀ [pl holes Hholes bagNew HbagNew s s']
  (Hn : HoldPiece pl holes Hholes bagNew HbagNew s = Some s'),
  Step pl s s'.
Proof. intros; eapply GuardedUpdateStep; [ intros; eapp HoldS6Step | exact Hn ]. Qed.

Lemma RotateKickPieceStep : ∀ [pl cw s s'] (Hn : RotateKickPiece pl cw s = Some s'), Step pl s s'.
Proof. intros; eapply GuardedUpdateStep; [ intros; eapp RotateKickS6Step | exact Hn ]. Qed.

(* In single-player mode, a fix changes the player's T6 state only. *)
Lemma FixPieceStep : ∀ [pl holes Hholes bagNew HbagNew s s']
  (Hn : FixPiece pl holes Hholes bagNew HbagNew s = Some s'),
  Step pl s s'.
Proof.
  intros; destruct (PlayerCount =? 1) eqn: Hm; [ | eapply StepFix; eassumption ].
  unfold FixPiece in Hn; rewrite Hm in Hn.
  eapply GuardedUpdateStep; [ intros; eapp FixS6Step | exact Hn ].
Qed.

Lemma FallStepCases : ∀ [pl holes Hholes bagNew HbagNew s s']
  (Hn : FallStep pl holes Hholes bagNew HbagNew s = Some s'),
  MovePiece pl (-1, 0)%Z s = Some s' ∨ FixPiece pl holes Hholes bagNew HbagNew s = Some s'.
Proof.
  intros; unfold FallStep in Hn; destruct (! WinnerMulti s pl); [ | discriminate Hn ].
  destruct MovePiece eqn: Em; [ inject Hn; subst | ]; tauto.
Qed.

(* Every event is a step, from the current state or, for Drop, from the state
 * where the piece is moved to its shadow. Events are told apart by the shape
 * of [Hn] (unifying an event with another one can take very long). *)
Lemma NextStep : ∀ [pl e s s'] (Hn : Next pl e s = Some s'),
  ∃ s0, (s0 = s ∨ s0 = NewPieceYXState (gy s pl, px s pl) pl s) ∧ Step pl s0 s'.
Proof.
  intros; destruct e; cbn [Next] in Hn;
    try match type of Hn with FallStep _ _ _ _ _ _ = _ =>
      apply FallStepCases in Hn; destruct Hn as [Hn | Hn] end;
    match type of Hn with
    | DropPiece _ _ _ _ _ _ = _ =>
        unfold DropPiece in Hn; eexists; split; [ right; reflexivity | ]
    | _ => exists s; split; [ left; reflexivity | ]
    end;
    match type of Hn with
    | MovePiece _ _ _ = _ => eapp MovePieceStep
    | RotatePiece _ _ _ = _ => eapp RotatePieceStep
    | HoldPiece _ _ _ _ _ _ = _ => eapp HoldPieceStep
    | RotateKickPiece _ _ _ = _ => eapp RotateKickPieceStep
    | FixPiece _ _ _ _ _ _ = _ => eapp FixPieceStep
    | ReceiveMessage _ _ _ = _ => eapply StepReceive; exact Hn
    | DisconnectPlayer _ _ = _ => eapply StepDisconnect; exact Hn
    | NoticeDisconnection _ _ = _ => eapply StepNotice; exact Hn
    | Some _ = _ => inject Hn; subst; apply StepStutter
    end.
Qed.

(* Takes a step apart. In each case, the new state is an explicit record, and
 * the guards of the event are hypotheses. A fix gives [E6], the T6 fix of the
 * player, and [Hgo], her game was not over. A receive gives [Em], the queue
 * popped, with its head [Hhead] and its tail [Htail] in the queue. *)
Ltac step_cases :=
  match goal with Hn : Step _ _ _ |- _ => destruct Hn end;
  repeat match goal with
  | _ : context [UpdatePlayer] |- _ => unfold UpdatePlayer in *
  | |- context [UpdatePlayer] => unfold UpdatePlayer
  | Hn : FixPiece ?pl _ _ ?bagNew ?HbagNew ?s = Some _,
    Hm : (PlayerCount =? 1) = false |- _ =>
      unfold FixPiece in Hn; rewrite Hm in Hn;
      destruct (! WinnerMulti s pl); [ | discriminate Hn ];
      let E6 := fresh "E6" in
      destruct (T6.FixPiece bagNew HbagNew (s6 s pl)) as [s6' | ] eqn: E6;
        cbn [option_map] in Hn; [ inject Hn; subst | discriminate Hn ];
      let Hgo := fresh "Hgo" in
      assert (Hgo : gameover s pl = false) by (apply T5P.FixPieceNotGameover in E6; exact E6);
      let Hc := fresh "Hc" in
      destruct (connected s pl) eqn: Hc
  | Hn : ReceiveMessage ?pl ?from ?s = Some _ |- _ =>
      unfold ReceiveMessage in Hn;
      let Hc := fresh "Hc" in let Em := fresh "Em" in
      destruct (connected s pl) eqn: Hc; [ | discriminate Hn ];
      destruct (messages s from pl) as [ | m ms] eqn: Em; [ discriminate Hn | ];
      let Hhead := fresh "Hhead" in let Htail := fresh "Htail" in
      assert (Hhead : In m (messages s from pl)) by (rewrite Em; left; reflexivity);
      assert (Htail : ∀ m', In m' ms → In m' (messages s from pl))
        by (rewrite Em; intros; right; assumption);
      destruct m; inject Hn; subst
  | Hn : DisconnectPlayer ?pl ?s = Some _ |- _ =>
      unfold DisconnectPlayer in Hn;
      let Hc := fresh "Hc" in
      destruct (connected s pl) eqn: Hc; [ inject Hn; subst | discriminate Hn ]
  | Hn : NoticeDisconnection ?pl ?s = Some _ |- _ =>
      unfold NoticeDisconnection in Hn;
      let Hc := fresh "Hc" in
      destruct (connected s pl) eqn: Hc; cbn [negb andb] in Hn; [ discriminate Hn | ];
      destruct (connectedView s pl pl); [ inject Hn; subst | discriminate Hn ]
  end.

(* Reads the fields of the explicit records. *)
Ltac fields := cbn [s6 garbage target gameoverView connectedView connected messages] in *.


(* ========================================================================= *)
(* Moving the piece to its shadow                                            *)
(*                                                                           *)
(* Drop fixes the piece after moving it to its shadow. The move changes only *)
(* the acting player's piece position, so it keeps every invariant.          *)
(* ========================================================================= *)

Lemma T1NewPieceYXStateSame : ∀ s1, T1.NewPieceYXState (T1.pyx s1) s1 = s1.
Proof. intros []; reflexivity. Qed.

(* The shadow is the piece's own position or a Valid one, and moving the piece
 * there leaves the shadow unchanged. *)
Lemma ShadowMoveCorrectWithoutGameover : ∀ [s6] (Hc : T6.CorrectWithoutGameover s6),
  T6.CorrectWithoutGameover (T6.NewPieceYXState (T6.gy s6, T6.px s6) s6).
Proof.
  intros; unfold T6.CorrectWithoutGameover, T6.NewPieceYXState, T6.gy, T6.px in *.
  assert (HG : T5.gy s6 = T5.ShadowY (T5.s4 s6))
    by (unfold T5.CorrectWithoutGameover, T5.GyEqShadowY in Hc; tauto).
  assert (HL : T5.LowestShadowY s6) by (unfold T5.CorrectWithoutGameover in Hc; tauto).
  assert (HC4 : T4.CorrectWithoutGameover (T5.s4 s6))
    by (unfold T5.CorrectWithoutGameover in Hc; tauto).
  assert (HC1 : T1.CorrectWithoutGameover (s1 s6))
    by (unfold T4.CorrectWithoutGameover, T3.CorrectWithoutGameover,
          T2.CorrectWithoutGameover in HC4; tauto).
  assert (HC1' : T1.CorrectWithoutGameover (T1.NewPieceYXState (T5.gy s6, T5.px s6) (s1 s6))). {
    destruct (T5P.ShadowYValidOrNoMove (T5.s4 s6)) as [E | HV].
    - assert (E' : (T5.gy s6, T5.px s6) = T1.pyx (s1 s6))
        by (rewrite HG, E; symmetry; apply surjective_pairing).
      rewrite E', T1NewPieceYXStateSame; exact HC1.
    - unfold T1.CorrectWithoutGameover in HC1.
      rewrite HG; apply T1P.NewPieceYXStateCorrectWithoutGameover; tauto.
  }
  assert (HL' : T5.LowestShadowY (T5.NewPieceYXState (T5.gy s6, T5.px s6) s6)). {
    unfold T5.LowestShadowY in *; cbn; intros Hgo.
    assert (HV : T5.ValidPieceCannotGoDown s6 (T5.gy s6)) by tauto.
    split_top; [ lia | exact HV | intros; lia ].
  }
  assert (HG' : T5.GyEqShadowY (T5.NewPieceYXState (T5.gy s6, T5.px s6) s6)). {
    unfold T5.GyEqShadowY; cbn; rewrite HG; symmetry.
    apply T5P.ShadowYIdempotent; first [ assumption | reflexivity ].
  }
  unfold T5.CorrectWithoutGameover, T4.CorrectWithoutGameover, T3.CorrectWithoutGameover,
    T2.CorrectWithoutGameover in *; cbn; tauto.
Qed.

Lemma NewPieceYXStateGameover : ∀ pyx pl s, gameover (NewPieceYXState pyx pl s) = gameover s.
Proof. intros; extensionality pl2; unfold gameover; cbn; player_cases; reflexivity. Qed.

Lemma NewPieceYXStateOtherS6 : ∀ [pyx pl s pl2] (Hne : pl2 ≠ pl),
  s6 (NewPieceYXState pyx pl s) pl2 = s6 s pl2.
Proof. intros; cbn; player_cases; first [ reflexivity | congruence ]. Qed.

Lemma NewPieceYXStateS6Correct : ∀ [s pl] (Hc : S6Correct s),
  S6Correct (NewPieceYXState (gy s pl, px s pl) pl s).
Proof.
  unfold S6Correct, Gameover, mg, gameover, gy, px; intros; cbn; player_cases;
    split_top; first [ apply ShadowMoveCorrectWithoutGameover | idtac ]; apply Hc.
Qed.

(* The other invariants read the state of a player only through gameover. *)
Lemma PreStepInvariants : ∀ [pl s s0]
  (Hs0 : s0 = s ∨ s0 = NewPieceYXState (gy s pl, px s pl) pl s),
    (S6Correct s → S6Correct s0)
  ∧ (SelfViewAccurate s → SelfViewAccurate s0)
  ∧ (ViewSound s → ViewSound s0)
  ∧ (MessageSound s → MessageSound s0)
  ∧ (NoSelfMessage s → NoSelfMessage s0)
  ∧ (LastMessagesGameoverDisconnect s → LastMessagesGameoverDisconnect s0)
  ∧ (TargetNotSelf s → TargetNotSelf s0)
  ∧ (TargetPlaying s → TargetPlaying s0).
Proof.
  intros; decompose [or] Hs0; subst; split_top; intros;
    first [ assumption | apply NewPieceYXStateS6Correct; assumption
          | unfold SelfViewAccurate, ViewSound, MessageSound, NoSelfMessage,
              LastMessagesGameoverDisconnect, TargetNotSelf, TargetPlaying, NoWinner, Playing,
              PlayingView in *;
            rewrite NewPieceYXStateGameover; assumption ].
Qed.

Lemma NewPieceYXStateCorrect : ∀ [s pl] (Hc : Correct s),
  Correct (NewPieceYXState (gy s pl, px s pl) pl s).
Proof.
  intros; pose proof (PreStepInvariants (pl := pl) (s := s) (or_intror eq_refl)).
  unfold Correct in *; tauto.
Qed.


(* ========================================================================= *)
(* OtherS6Unchanged, and monotonicity of gameover, connected and the views   *)
(* ========================================================================= *)

(* A step changes the T6 state of the acting player only. *)
Lemma StepOtherS6Unchanged : ∀ [pl s s' pl2]
  (Hn : Step pl s s')
  (Hne : pl2 ≠ pl),
  s6 s' pl2 = s6 s pl2.
Proof. intros; step_cases; fields; player_cases; first [ reflexivity | congruence ]. Qed.

(* Only the acting player's gameover can change, and only from false: a fix
 * needs a game not over. *)
Lemma StepGameoverMonotone : ∀ [pl s s' pl2]
  (Hn : Step pl s s')
  (Hg : gameover s pl2 = true),
  gameover s' pl2 = true.
Proof.
  intros; step_cases; unfold gameover in *; fields; player_cases;
    first [ assumption | congruence | unfold S6Step in *; tauto ].
Qed.

(* Only DisconnectPlayer changes connected, and only to false. *)
Lemma StepDisconnectedMonotone : ∀ [pl s s' pl2]
  (Hn : Step pl s s')
  (Hc : connected s pl2 = false),
  connected s' pl2 = false.
Proof. intros; step_cases; fields; player_cases; first [ assumption | reflexivity ]. Qed.

(* The view of the acting player about herself follows her gameover, which is
 * monotone; it is not true before a fix, which needs a game not over. A received
 * GameoverMessage sets a view to true. *)
Lemma StepGameoverViewMonotone : ∀ [pl s s' pl2 pl3]
  (Ha : SelfViewAccurate s)
  (Hn : Step pl s s')
  (Hg : gameoverView s pl2 pl3 = true),
  gameoverView s' pl2 pl3 = true.
Proof.
  intros; step_cases; unfold SelfViewAccurate, gameover in *; fields; player_cases;
    first [ reflexivity | assumption | rewrite Ha in Hg; first [ congruence | unfold S6Step in *; tauto ] ].
Qed.

(* Only a received DisconnectMessage and NoticeDisconnection change
 * connectedView, and only to false. *)
Lemma StepDisconnectedViewMonotone : ∀ [pl s s' pl2 pl3]
  (Hn : Step pl s s')
  (Hc : connectedView s pl2 pl3 = false),
  connectedView s' pl2 pl3 = false.
Proof. intros; step_cases; fields; player_cases; first [ assumption | reflexivity ]. Qed.

(* States both monotonicity facts of the step [Hn]. *)
Ltac monotone_facts :=
  match goal with Hn : Step ?pl ?s ?s' |- _ =>
    assert (Hgm : ∀ pl2, gameover s pl2 = true → gameover s' pl2 = true)
      by (intros; eapp StepGameoverMonotone);
    assert (Hcm : ∀ pl2, connected s pl2 = false → connected s' pl2 = false)
      by (intros; eapp StepDisconnectedMonotone)
  end.

(* A player who plays after a step played before it. *)
Lemma PlayingBackward : ∀ [pl s s' pl2]
  (Hn : Step pl s s')
  (Hp : Playing s' pl2 = true),
  Playing s pl2 = true.
Proof.
  unfold Playing; intros; monotone_facts.
  apply andb_true_iff in Hp as [Hg Hc]; apply negb_true_iff in Hg.
  destruct (gameover s pl2) eqn: Eg; [ apply Hgm in Eg; congruence | ].
  destruct (connected s pl2) eqn: Ec; [ reflexivity | apply Hcm in Ec; congruence ].
Qed.

Lemma NoWinnerBackward : ∀ [pl s s']
  (Hn : Step pl s s')
  (Hw : NoWinner s'),
  NoWinner s.
Proof.
  intros; destruct Hw as (pl1 & pl2 & Hne & H1 & H2).
  exists pl1, pl2; split_top; first [ assumption | eapp PlayingBackward ].
Qed.


(* ========================================================================= *)
(* SelfViewAccurate                                                          *)
(* ========================================================================= *)

(* A player can receive no message from herself (NoSelfMessage). *)
Ltac no_self_receive Hm :=
  match goal with H : In _ (messages _ ?p ?p) |- _ => rewrite Hm in H; destruct H end.

(* The acting player's view of herself follows her gameover. Other updates of
 * gameoverView come from messages, which are never from oneself. *)
Lemma StepSelfViewAccurate : ∀ [pl s s']
  (Ha : SelfViewAccurate s)
  (Hm : NoSelfMessage s)
  (Hn : Step pl s s'),
  SelfViewAccurate s'.
Proof.
  unfold SelfViewAccurate, NoSelfMessage, gameover; intros; step_cases; fields; player_cases;
    first [ reflexivity | apply Ha | no_self_receive Hm ].
Qed.


(* ========================================================================= *)
(* MessageSound                                                              *)
(* ========================================================================= *)

Lemma MessageSoundGameover : ∀ [s from to]
  (Hs : MessageSound s)
  (Hin : In GameoverMessage (messages s from to)),
  gameover s from = true.
Proof. intros; apply Hs in Hin; exact Hin. Qed.

Lemma MessageSoundDisconnect : ∀ [s from to]
  (Hs : MessageSound s)
  (Hin : In DisconnectMessage (messages s from to)),
  connected s from = false.
Proof. intros; apply Hs in Hin; exact Hin. Qed.

(* Takes apart the membership of a message in a queue, as a step builds it. *)
Ltac in_cases :=
  repeat match goal with
  | H : In _ (_ ++ _) |- _ => apply in_app_or in H; destruct H as [H | H]
  | H : In _ (_ :: _) |- _ => destruct H as [H | H]
  | H : In _ [] |- _ => destruct H
  | H : In _ (if ?b then _ else _) |- _ => revert H; destruct b; intro H
  | H : In _ ?ms, Ht : ∀ m, In m ?ms → In m _ |- _ => apply Ht in H
  | H : _ = _ |- _ => discriminate H
  end.

(* A message in a queue was already there, and stays sound by monotonicity, or
 * was just sent: a GameoverMessage by a fix that made its sender gameover, a
 * DisconnectMessage by the disconnection of its sender. *)
Lemma StepMessageSound : ∀ [pl s s']
  (Hs : MessageSound s)
  (Hn : Step pl s s'),
  MessageSound s'.
Proof.
  intros; monotone_facts; intros from to; split_top; intros Hin;
    step_cases; fields; unfold SendMessages in *; player_cases; in_cases;
    first [ reflexivity | eapp MessageSoundDisconnect
          | apply Hgm; eapp MessageSoundGameover | apply Hcm; eapp MessageSoundDisconnect
          | unfold gameover; fields; player_cases; reflexivity ].
Qed.


(* ========================================================================= *)
(* ViewSound                                                                 *)
(* ========================================================================= *)

Lemma ViewSoundGameover : ∀ [s pl1 pl2]
  (Hv : ViewSound s)
  (Hg : gameoverView s pl1 pl2 = true),
  gameover s pl2 = true.
Proof. intros; apply Hv in Hg; exact Hg. Qed.

Lemma ViewSoundConnected : ∀ [s pl1 pl2]
  (Hv : ViewSound s)
  (Hc : connectedView s pl1 pl2 = false),
  connected s pl2 = false.
Proof. intros; apply Hv in Hc; exact Hc. Qed.

(* A view stays sound by monotonicity, or is updated: by the acting player
 * about herself, from a received message (sound by MessageSound), or by
 * NoticeDisconnection, whose guard is the truth. *)
Lemma StepViewSound : ∀ [pl s s']
  (Hv : ViewSound s)
  (Hs : MessageSound s)
  (Hn : Step pl s s'),
  ViewSound s'.
Proof.
  intros; monotone_facts; intros pl1 pl2; split_top; intros Hin;
    step_cases; fields; player_cases;
    first [ reflexivity | assumption | eapp ViewSoundConnected | eapp MessageSoundDisconnect
          | apply Hgm; first [ eapp ViewSoundGameover | eapp MessageSoundGameover ]
          | apply Hcm; eapp ViewSoundConnected
          | unfold gameover; fields; player_cases; assumption ].
Qed.


(* ========================================================================= *)
(* NoSelfMessage                                                             *)
(* ========================================================================= *)

(* Messages are only sent to others, and only popped from a non-self queue. *)
Lemma StepNoSelfMessage : ∀ [pl s s']
  (Hm : NoSelfMessage s)
  (Hn : Step pl s s'),
  NoSelfMessage s'.
Proof.
  unfold NoSelfMessage; intros; step_cases; fields; unfold SendMessages; player_cases;
    first [ apply Hm | no_self_receive Hm ].
Qed.


(* ========================================================================= *)
(* LastMessagesGameoverDisconnect                                            *)
(* ========================================================================= *)

(* The shape of a queue required by LastMessagesGameoverDisconnect. *)
Definition QueueShape (q : list Message) : Prop :=
  ∃ (ns : list ℕ) (b1 b2 : bool),
    q = map GarbageMessage ns
      ++ (if b1 then [GameoverMessage] else [])
      ++ (if b2 then [DisconnectMessage] else []).

Lemma LastMessagesQueueShape : ∀ [s from to]
  (Hl : LastMessagesGameoverDisconnect s)
  (Hne : from ≠ to),
  QueueShape (messages s from to).
Proof. intros; exact (Hl from to Hne). Qed.

(* A fix appends some garbage and a gameover to a queue of garbage only. *)
Lemma QueueShapeFix : ∀ [q] (b g : bool) n
  (Hq : QueueShape q)
  (Hg : ¬ In GameoverMessage q)
  (Hd : ¬ In DisconnectMessage q),
  QueueShape (q ++ (if b then [GarbageMessage n] else []) ++ (if g then [GameoverMessage] else [])).
Proof.
  intros; destruct Hq as (ns & b1 & b2 & E); subst q.
  destruct b1; [ exfalso; apply Hg; apply in_app_iff; right; left; reflexivity | ].
  destruct b2; [ exfalso; apply Hd; apply in_app_iff; right; left; reflexivity | ].
  exists (ns ++ if b then [n] else []), g, false.
  destruct b; cbn; rewrite ?map_app, ?app_nil_r, <- ?app_assoc; reflexivity.
Qed.

(* A disconnection appends a disconnect to a queue without one. *)
Lemma QueueShapeDisconnect : ∀ [q]
  (Hq : QueueShape q)
  (Hd : ¬ In DisconnectMessage q),
  QueueShape (q ++ [DisconnectMessage]).
Proof.
  intros; destruct Hq as (ns & b1 & b2 & E); subst q.
  destruct b2; [ exfalso; apply Hd; rewrite !in_app_iff; cbn; tauto | ].
  exists ns, b1, true; cbn; rewrite app_nil_r, <- app_assoc; reflexivity.
Qed.

Lemma QueueShapePop : ∀ [m q]
  (Hq : QueueShape (m :: q)),
  QueueShape q.
Proof.
  intros; destruct Hq as ([ | n ns] & b1 & b2 & E);
    [ destruct b1; [ | destruct b2 ] | ]; cbn in E; inversion E; subst;
    first [ exists [], false, b2; reflexivity | exists [], false, false; reflexivity
          | exists ns, b1, b2; reflexivity ].
Qed.

(* The sender of a fix is not gameover, and the sender of a fix or of a
 * disconnection is connected: by MessageSound, its queues hold no gameover or
 * disconnect message yet. *)
Lemma StepLastMessagesGameoverDisconnect : ∀ [pl s s']
  (Hl : LastMessagesGameoverDisconnect s)
  (Hs : MessageSound s)
  (Hm : NoSelfMessage s)
  (Hn : Step pl s s'),
  LastMessagesGameoverDisconnect s'.
Proof.
  intros; step_cases; intros pl1 pl2 Hne;
    match goal with |- ∃ _ _ _, ?q = _ => change (QueueShape q) end;
    fields; unfold SendMessages; player_cases;
    first
    [ eapp LastMessagesQueueShape
    | match goal with E : messages _ _ _ = _ :: ?q |- QueueShape ?q =>
        eapply QueueShapePop; rewrite <- E; eapp LastMessagesQueueShape end
    | first [ apply QueueShapeFix | apply QueueShapeDisconnect ];
        first [ eapp LastMessagesQueueShape
              | intro Hin; apply MessageSoundGameover in Hin; [ congruence | assumption ]
              | intro Hin; apply MessageSoundDisconnect in Hin; [ congruence | assumption ] ] ].
Qed.


(* ========================================================================= *)
(* TargetNotSelf and TargetPlaying                                           *)
(*                                                                           *)
(* Both are proven together (see [Targets]): a target keeps its value and    *)
(* the view of it, or is redirected by NextTarget to another player who is   *)
(* playing as far as the redirecting player knows.                           *)
(* ========================================================================= *)

Lemma IterSuccR : ∀ (f : Player → Player) n x, (f ** (S n)) x = (f ** n) (f x).
Proof. intros f n; induction n as [ | n IH ]; intros; [ | simpl; rewrite <- IH ]; reflexivity. Qed.

(* NextTargetAux returns self only if none of the players it checks is
 * playing and other than self. *)
Lemma NextTargetAuxSelf : ∀ fuel playing self pl
  (H : NextTargetAux fuel playing self pl = self)
  k (Hk : k < fuel),
  playing ((PlayerNext ** S k) pl) = false ∨ (PlayerNext ** S k) pl = self.
Proof.
  induction fuel as [ | fuel IH ]; intros; [ lia | cbn [NextTargetAux] in H ].
  destruct (playing (PlayerNext pl) && ! PlayerEqb (PlayerNext pl) self) eqn: Ec.
  - apply andb_true_iff in Ec as [_ Ec]; apply negb_true_iff, PlayerEqbFalse in Ec; contradiction.
  - destruct k as [ | k ]; [ | rewrite IterSuccR; apply IH; [ assumption | lia ] ].
    apply andb_false_iff in Ec; destruct Ec as [Ec | Ec];
      [ left | right; apply negb_false_iff, PlayerEqbTrue in Ec ]; exact Ec.
Qed.

(* Any other result of NextTargetAux passed its playing test. *)
Lemma NextTargetAuxPlaying : ∀ fuel playing self pl
  (H : NextTargetAux fuel playing self pl ≠ self),
  playing (NextTargetAux fuel playing self pl) = true.
Proof.
  induction fuel as [ | fuel IH ]; intros; cbn [NextTargetAux] in *; [ contradiction | ].
  destruct (playing (PlayerNext pl) && ! PlayerEqb (PlayerNext pl) self) eqn: Ec;
    [ apply andb_true_iff in Ec; tauto | auto ].
Qed.

(* When another player passes the playing test, NextTarget finds one: the
 * search checks PlayerCount players, i.e. all of them (PlayerCyclicPermutation). *)
Lemma NextTargetSpec : ∀ [playing self] start [pl2]
  (Hne : pl2 ≠ self)
  (Hp : playing pl2 = true),
  NextTarget playing self start ≠ self ∧ playing (NextTarget playing self start) = true.
Proof.
  intros; unfold NextTarget.
  destruct (PlayerCyclicPermutation (PlayerNext start) pl2) as (k & (Hk & E) & _).
  assert (HR : NextTargetAux PlayerCount playing self start ≠ self). {
    intro HR; apply NextTargetAuxSelf with (k := k) in HR; [ | assumption ].
    rewrite IterSuccR, E in HR; destruct HR; congruence.
  }
  split_top; [ assumption | apply NextTargetAuxPlaying; assumption ].
Qed.

Lemma NoWinnerOther : ∀ [s] pl
  (Hw : NoWinner s),
  ∃ pl2, pl2 ≠ pl ∧ Playing s pl2 = true.
Proof.
  intros; destruct Hw as (pl1 & pl2 & Hne & H1 & H2).
  destruct (PlayerEqb pl1 pl) eqn: E;
    [ apply PlayerEqbTrue in E; subst; exists pl2 | apply PlayerEqbFalse in E; exists pl1 ];
    split_top; auto.
Qed.

Lemma ViewSoundPlaying : ∀ [s pl pl2]
  (Hv : ViewSound s)
  (Hp : Playing s pl2 = true),
  PlayingView s pl pl2 = true.
Proof.
  unfold Playing, PlayingView; intros.
  apply andb_true_iff in Hp as [Hg Hc]; apply negb_true_iff in Hg.
  destruct (gameoverView s pl pl2) eqn: Egv; [ apply Hv in Egv; congruence | ].
  destruct (connectedView s pl pl2) eqn: Ecv; [ reflexivity | apply Hv in Ecv; congruence ].
Qed.

(* A redirected target is another player passing the playing test, as long as
 * the test accepts every other player really playing: there is one, since
 * there is no winner. *)
Lemma Redirect : ∀ [s pl] (playing : Player → bool) start
  (Hv : ViewSound s)
  (Hw : NoWinner s)
  (Hp : ∀ pl2, pl2 ≠ pl → Playing s pl2 = true → playing pl2 = true),
  NextTarget playing pl start ≠ pl ∧ playing (NextTarget playing pl start) = true.
Proof.
  intros; apply (NoWinnerOther pl) in Hw as (pl2 & Hne & Hp2).
  apply NextTargetSpec with (pl2 := pl2); auto.
Qed.

(* On receiving the death or disconnection of `from`, pl redirects her target
 * to a player other than herself and from, and playing as far as she knows. *)
Lemma ReceiveRedirect : ∀ [s pl from]
  (Hv : ViewSound s)
  (Hw : NoWinner s)
  (Hf : Playing s from = false),
  let R := NextTarget (λ pl2, if PlayerEqb pl2 from then false else PlayingView s pl pl2) pl from in
  R ≠ pl ∧ R ≠ from ∧ PlayingView s pl R = true.
Proof.
  intros.
  assert (HR : R ≠ pl ∧ (if PlayerEqb R from then false else PlayingView s pl R) = true). {
    unfold R; apply Redirect with (s := s);
      first [ assumption | intros pl2 Hne Hp; player_cases; first [ congruence | eapp ViewSoundPlaying ] ].
  }
  destruct HR as [HR1 HR2]; all_player_cases; split_top; first [ assumption | discriminate HR2 ].
Qed.

Definition Targets (s : State) : Prop :=
  ∀ pl, target s pl ≠ pl ∧ PlayingView s pl (target s pl) = true.

Lemma TargetsIff : ∀ s,
  (PlayerCount > 1 → NoWinner s → Targets s) ↔ TargetNotSelf s ∧ TargetPlaying s.
Proof. unfold Targets, TargetNotSelf, TargetPlaying; firstorder. Qed.

Lemma TargetsNotSelf : ∀ [s pl] (Ht : Targets s), target s pl ≠ pl.
Proof. intros; apply Ht. Qed.

Lemma TargetsPlaying : ∀ [s pl] (Ht : Targets s), PlayingView s pl (target s pl) = true.
Proof. intros; apply Ht. Qed.

(* Comparisons other than with a redirected target. *)
Ltac not_redirected a b :=
  lazymatch a with NextTarget _ _ _ => fail | _ =>
  lazymatch b with NextTarget _ _ _ => fail | _ => idtac end end.

(* A kept target is not oneself; a redirected one is not the redirecting
 * player (see [Redirect]). *)
Lemma StepTargetNotSelf : ∀ [pl s s']
  (Ht : NoWinner s → ∀ pl, target s pl ≠ pl)
  (Hv : ViewSound s)
  (Hs : MessageSound s)
  (Hn : Step pl s s')
  (Hw : NoWinner s'),
  ∀ pl, target s' pl ≠ pl.
Proof.
  intros pl s s' Ht Hv Hs Hn Hw.
  assert (Hw0 : NoWinner s) by eapp NoWinnerBackward.
  assert (Ht0 : ∀ pl, target s pl ≠ pl) by auto.
  step_cases; intros p; fields;
    try match goal with |- context [if ?c then NextTarget _ _ _ else _] => destruct c eqn: Ec end;
    player_cases_if not_redirected;
    first
    [ discriminate
    | contradiction
    | match goal with |- target s _ ≠ _ => apply Ht0 end
    | match goal with |- NextTarget ?playing ?self ?start ≠ _ =>
        enough (HR : NextTarget playing self start ≠ self
                   ∧ playing (NextTarget playing self start) = true)
          by tauto;
        apply (Redirect (s := s) playing start);
          first [ assumption
                | intros pl2 Hne Hp; unfold FP.PlayingView', FP.GameoverView'; player_cases;
                  first [ contradiction | eapp ViewSoundPlaying ] ]
      end
    | match goal with |- NextTarget _ ?pl ?from ≠ _ =>
        assert (Hf : Playing s from = false)
          by (unfold Playing; first
               [ erewrite MessageSoundGameover by eassumption; reflexivity
               | erewrite MessageSoundDisconnect by eassumption; apply andb_false_r ]);
        apply (ReceiveRedirect (pl := pl)) in Hf as (HR1 & HR2 & HR3);
          first [ assumption | exact HR1 ]
      end ].
Qed.

(* A kept target is not oneself, so the view of it is not the one the acting
 * player has of herself; a received message updates the view of its sender,
 * who is the target only when it is redirected. *)
Lemma StepTargets : ∀ [pl s s']
  (Ht : NoWinner s → Targets s)
  (Hv : ViewSound s)
  (Hs : MessageSound s)
  (Hn : Step pl s s')
  (Hw : NoWinner s'),
  Targets s'.
Proof.
  intros.
  assert (Hw0 : NoWinner s) by eapp NoWinnerBackward.
  assert (Ht0 : Targets s) by auto.
  step_cases; intros p; unfold PlayingView; fields;
    try match goal with |- context [if ?c then NextTarget _ _ _ else _] => destruct c eqn: Ec end;
    player_cases_if not_redirected;
    first
    [ congruence
    | exfalso; eapp TargetsNotSelf
    | split_top; [ eapp TargetsNotSelf | eapp TargetsPlaying ]
    | (* redirected on a fix: the test is the post-fix view of the fixing player *)
      match goal with |- NextTarget ?playing _ ?start ≠ _ ∧ _ =>
        apply (Redirect (s := s) playing start);
          first [ assumption
                | intros pl2 Hne Hp; unfold FP.PlayingView', FP.GameoverView'; player_cases;
                  first [ contradiction | eapp ViewSoundPlaying ] ]
      end
    | (* redirected on a message: its sender is not playing (MessageSound) *)
      match goal with |- NextTarget _ ?pl ?from ≠ _ ∧ _ =>
        assert (Hf : Playing s from = false)
          by (unfold Playing; first
               [ erewrite MessageSoundGameover by eassumption; reflexivity
               | erewrite MessageSoundDisconnect by eassumption; apply andb_false_r ]);
        apply (ReceiveRedirect (pl := pl)) in Hf as (HR1 & HR2 & HR3);
          first [ assumption
                | unfold PlayingView in *; rewrite (PlayerNeqb HR2); split_top; assumption ]
      end ].
Qed.


(* ========================================================================= *)
(* S6Correct                                                                 *)
(*                                                                           *)
(* A multiplayer fix replaces the main grid by the cropped grid with garbage *)
(* (FP.CroppedMg'). It keeps the box of the main grid, and has no full line: *)
(* a garbage row has a hole, and a row above the garbage is a row of the     *)
(* main grid.                                                                *)
(* ========================================================================= *)

Lemma FixMgBox : ∀ s pl s6' holes
  (EHW : HW (T6.mg s6') = HW InitialMainGrid)
  (EYX : YX (T6.mg s6') = YX InitialMainGrid),
    HW (FP.CroppedMg' s pl s6' holes) = HW InitialMainGrid
  ∧ YX (FP.CroppedMg' s pl s6' holes) = YX InitialMainGrid.
Proof.
  intros; destruct AxiomsInitialMainGrid as (HH & HW0 & HYX & _).
  unfold FP.CroppedMg', FP.Mg', T1.Full, T1.Constant, GarbageGrid.
  unfold GridUnion, GridIntersect, GridTranslate, H, W, Y, X in *.
  cbn [HW YX fst snd]; rewrite EHW, EYX, HYX in *; cbn [fst snd].
  split; [ rewrite (surjective_pairing (HW InitialMainGrid)) | ]; f_equal; cbn [fst snd]; lia.
Qed.

Lemma FixMgL : ∀ s pl s6' holes y x,
  let rem := Z.of_nat (snd (GenRemGarbage (garbage s pl) (T6.clearedLines s6') (T6.perfectClear s6'))) in
  L (FP.CroppedMg' s pl s6' holes) y x =
       (0 ≤? y <? rem) && (0 ≤? x <? W InitialMainGrid) && (x ≠? Z.of_nat (holes y))
    || L (T6.mg s6') (y - rem) (x - 0) && (rem ≤? y)%Z.
Proof. intros; cbn; rewrite andb_true_r; reflexivity. Qed.

Lemma FixMgNoFullLine : ∀ [s pl s6' holes]
  (Hholes : ValidHoles holes)
  (EHW : HW (T6.mg s6') = HW InitialMainGrid)
  (EYX : YX (T6.mg s6') = YX InitialMainGrid)
  (HN : ¬ T1.HasFullLine (T6.mg s6')),
  ¬ T1.HasFullLine (FP.CroppedMg' s pl s6' holes).
Proof.
  intros.
  assert (EB' : HW (FP.CroppedMg' s pl s6' holes) = HW InitialMainGrid
              ∧ YX (FP.CroppedMg' s pl s6' holes) = YX InitialMainGrid)
    by (apply FixMgBox; assumption).
  destruct EB' as [EHW' EYX']; destruct AxiomsInitialMainGrid as (_ & _ & HYX & _).
  unfold T1.HasFullLine, T1.IsFullLine in *.
  assert (EB : ∀ g, HW g = HW InitialMainGrid → YX g = YX InitialMainGrid →
      Y g = 0%Z ∧ X g = 0%Z ∧ H g = H InitialMainGrid ∧ W g = W InitialMainGrid)
    by (intros g E1 E2; unfold Y, X, H, W; rewrite E1, E2, HYX; split_top; reflexivity).
  apply EB in EHW' as (-> & -> & -> & ->); [ | assumption ].
  apply EB in EHW as (EY & EX & EH & EW); [ | assumption ].
  rewrite EY, EX, EH, EW in HN.
  intros (y & Hy & HF).
  set (rem := Z.of_nat (snd (GenRemGarbage (garbage s pl) (T6.clearedLines s6') (T6.perfectClear s6')))) in *.
  destruct (Z_lt_le_dec y rem) as [Hlt | Hge].
  - (* a garbage row has a hole *)
    assert (HF' : L (FP.CroppedMg' s pl s6' holes) y (Z.of_nat (holes y)) = true)
      by (apply HF; apply Hholes).
    rewrite FixMgL, Z.eqb_refl, andb_false_r in HF'; fold rem in HF'; cbn [negb orb] in HF'.
    rewrite (proj2 (Z.leb_gt rem y) Hlt), andb_false_r in HF'; discriminate HF'.
  - (* a row above the garbage is a row of the main grid *)
    apply HN; exists (y - rem)%Z; split; [ lia | intros x Hx ].
    specialize (HF x Hx); rewrite FixMgL in HF; fold rem in HF.
    rewrite (proj2 (Z.ltb_ge y rem) Hge), andb_false_r, Z.sub_0_r in HF; cbn [andb orb] in HF.
    apply andb_true_iff in HF; tauto.
Qed.

(* The new T6 state of the fixing player has the T6 fix's piece and fields,
 * and the cropped grid with garbage. Its shadow is recomputed, so the T5
 * invariants follow from the T4 ones (T5Proofs' LiftCorrectWithoutGameover). *)
Lemma FixMultiCorrect : ∀ [s pl bagNew HbagNew s6'] holes
  (Hholes : ValidHoles holes)
  (Hc : T6.CorrectWithoutGameover (s6 s pl))
  (E6 : T6.FixPiece bagNew HbagNew (s6 s pl) = Some s6'),
  let s6New := NewMainGridGameoverState
    (FP.CroppedMg' s pl s6' holes) (FP.Gameover' s pl s6' holes) s6' in
  T6.CorrectWithoutGameover s6New ∧ S6Gameover s6New.
Proof.
  intros.
  assert (Hc' : T6.CorrectWithoutGameover s6') by eapp T5P.FixPieceCorrectWithoutGameover.
  assert (HC4 : T4.CorrectWithoutGameover (T5.s4 s6'))
    by (unfold T6.CorrectWithoutGameover, T5.CorrectWithoutGameover in Hc'; tauto).
  assert (HT : T1.TypeOK (s1 s6') ∧ T1.NoFullLine (s1 s6')) by
    (unfold T4.CorrectWithoutGameover, T3.CorrectWithoutGameover, T2.CorrectWithoutGameover,
       T1.CorrectWithoutGameover in HC4; tauto).
  destruct HT as ((EHW & EYX & Epr) & HN).
  assert (EB : HW (FP.CroppedMg' s pl s6' holes) = HW InitialMainGrid
             ∧ YX (FP.CroppedMg' s pl s6' holes) = YX InitialMainGrid)
    by (apply FixMgBox; assumption).
  destruct EB as [EHW' EYX'].
  destruct (T5P.FixPieceFreshPiece E6) as (pNew & Ep & Epyx & Epr0).
  assert (Hsw : T3.swapped (T4.s3 (T5.s4 s6')) = false) by eapp T5P.FixPieceSwappedFalse.
  assert (HG : S6Gameover s6New). {
    unfold S6Gameover; intros E; change (FP.Gameover' s pl s6' holes = true).
    unfold FP.Gameover'; apply orb_true_iff; right; exact E.
  }
  assert (HP : T1.PieceOccupiedInsideBounds (s1 s6New) ∧ T1.PieceOnFreeBlocks (s1 s6New))
    by (apply T1P.NewPieceInvariants; first
          [ exact HG | exact EHW' | exact EYX'
          | change (T1.pyx (s1 s6') = T1.InitialYX (T1.p (s1 s6'))); congruence
          | change (T1.pr (s1 s6') = 0%Z); assumption ]).
  assert (HN' : T1.NoFullLine (s1 s6New)) by (apply FixMgNoFullLine; assumption).
  assert (HC4' : T4.CorrectWithoutGameover (T5.s4 s6New)) by
    (unfold T4.CorrectWithoutGameover, T3.CorrectWithoutGameover, T2.CorrectWithoutGameover,
       T1.CorrectWithoutGameover, T3.GameoverImplyNotSwapped, T1.TypeOK in *; cbn; tauto).
  split; [ apply T5P.LiftCorrectWithoutGameover; [ exact HC4' | reflexivity ] | exact HG ].
Qed.

Lemma S6StepCorrect : ∀ [s6 s6']
  (H6 : S6Step s6 s6')
  (Hc : T6.CorrectWithoutGameover s6 ∧ S6Gameover s6),
  T6.CorrectWithoutGameover s6' ∧ S6Gameover s6'.
Proof. unfold S6Step; intros; tauto. Qed.

(* Only the acting player's T6 state changes. *)
Lemma StepS6Correct : ∀ [pl s s']
  (Hc : S6Correct s)
  (Hn : Step pl s s'),
  S6Correct s'.
Proof.
  unfold S6Correct, Gameover, mg, gameover; fold S6Gameover; intros; step_cases;
    fields; player_cases;
    first [ apply Hc | eapply S6StepCorrect; [ eassumption | apply Hc ]
          | eapply FixMultiCorrect; first [ eassumption | apply Hc ] ].
Qed.


(* ========================================================================= *)
(* State invariants                                                          *)
(* ========================================================================= *)

Lemma PlayerNextNotSelf : ∀ (Hc : PlayerCount > 1) pl, PlayerNext pl ≠ pl.
Proof.
  intros Hc pl E; destruct (PlayerCyclicPermutation pl pl) as (n & _ & Hu).
  assert (E0 : n = 0) by (apply Hu; split; [ lia | reflexivity ]).
  assert (E1 : n = 1) by (apply Hu; split; [ lia | exact E ]).
  lia.
Qed.

(* Each player is T6-correct, knows only herself, and has no message yet. Her
 * target is her successor, which is not herself in multiplayer mode. *)
Lemma InitCorrect : ∀ bags H, Correct (Init bags H).
Proof.
  intros.
  assert (HS : S6Correct (Init bags H)). {
    intros pl; pose proof (T6P.InitCorrect (bags pl) (H pl)) as Hc.
    unfold Gameover, mg, gameover; cbn [s6 Init].
    unfold T6.Correct, T5.Correct, T4.Correct, T3.Correct, T2.Correct, T1.Correct, T1.Gameover,
      T6.CorrectWithoutGameover, T5.CorrectWithoutGameover, T4.CorrectWithoutGameover,
      T3.CorrectWithoutGameover, T2.CorrectWithoutGameover, T6.gameover, T5.gameover,
      T4.gameover, T3.gameover, T2.gameover, T6.mg, T5.mg, T4.mg, T3.mg, T2.mg in *.
    tauto.
  }
  assert (HT : PlayerCount > 1 → NoWinner (Init bags H) → Targets (Init bags H)). {
    intros Hc _ pl; unfold PlayingView; cbn.
    rewrite (PlayerNeqb (PlayerNextNotSelf Hc pl)).
    split_top; [ apply PlayerNextNotSelf; assumption | apply Z.gtb_lt; lia ].
  }
  apply TargetsIff in HT.
  unfold Correct, SelfViewAccurate, ViewSound, MessageSound, NoSelfMessage,
    LastMessagesGameoverDisconnect, gameover; cbn.
  split_top; intros; player_cases;
    first [ assumption | tauto | split_top; intros; first [ assumption | discriminate | contradiction ]
          | exists [], false, false; reflexivity ].
Qed.

Lemma StepCorrect : ∀ [pl s s']
  (Hc : Correct s)
  (Hn : Step pl s s'),
  Correct s'.
Proof.
  intros; unfold Correct in *; decompose [and] Hc.
  assert (HT : PlayerCount > 1 → NoWinner s → Targets s) by (apply TargetsIff; split_top; assumption).
  assert (HT' : PlayerCount > 1 → NoWinner s' → Targets s') by (intros; eapply StepTargets; eauto).
  apply TargetsIff in HT'.
  split_top;
    first [ tauto | eapp StepS6Correct | eapp StepSelfViewAccurate | eapp StepViewSound
          | eapp StepMessageSound | eapp StepNoSelfMessage | eapp StepLastMessagesGameoverDisconnect ].
Qed.

Lemma NextCorrect : ∀ [pl e s s']
  (Hc : Correct s)
  (Hn : Next pl e s = Some s'),
  Correct s'.
Proof.
  intros; apply NextStep in Hn as (s0 & Hs0 & Hn).
  assert (Hc0 : Correct s0)
    by (decompose [or] Hs0; subst; first [ assumption | apply NewPieceYXStateCorrect; assumption ]).
  eapp StepCorrect.
Qed.

(* Initial facts of a single invariant. *)
Ltac init_part :=
  intros bags H; pose proof (InitCorrect bags H) as Hc; unfold Correct in Hc;
  decompose [and] Hc; assumption.

(* Replaces the step [Hn] by a Step from a state s0, and states how each
 * invariant carries over from s to s0. *)
Ltac next_step :=
  match goal with H : Next _ _ _ = Some _ |- _ =>
    apply NextStep in H as (s0 & Hs0 & Hn);
    apply PreStepInvariants in Hs0; decompose [and] Hs0; clear Hs0
  end.

Theorem SpecS6Correct :
   (∀ bags H, S6Correct (Init bags H))
 ∧ (∀ [pl e s s']
      (H1 : S6Correct s)
      (H2 : Next pl e s = Some s'),
      S6Correct s').
Proof. split_top; [ init_part | intros; next_step; apply StepS6Correct in Hn; eauto ]. Qed.

Theorem SpecSelfViewAccurate :
   (∀ bags H, SelfViewAccurate (Init bags H))
 ∧ (∀ [pl e s s']
      (H1 : NoSelfMessage s)
      (H2 : SelfViewAccurate s)
      (H3 : Next pl e s = Some s'),
      SelfViewAccurate s').
Proof. split_top; [ init_part | intros; next_step; apply StepSelfViewAccurate in Hn; eauto ]. Qed.

Theorem SpecMessageSound :
   (∀ bags H, MessageSound (Init bags H))
 ∧ (∀ [pl e s s']
      (Hc : MessageSound s)
      (H1 : Next pl e s = Some s'),
      MessageSound s').
Proof. split_top; [ init_part | intros; next_step; apply StepMessageSound in Hn; eauto ]. Qed.

Theorem SpecViewSound :
   (∀ bags H, ViewSound (Init bags H))
 ∧ (∀ [pl e s s']
      (H1 : ViewSound s)
      (H2 : MessageSound s)
      (H3 : Next pl e s = Some s'),
      ViewSound s').
Proof. split_top; [ init_part | intros; next_step; apply StepViewSound in Hn; eauto ]. Qed.

Theorem SpecNoSelfMessage :
   (∀ bags H, NoSelfMessage (Init bags H))
 ∧ (∀ [pl e s s']
      (H1 : NoSelfMessage s)
      (H2 : Next pl e s = Some s'),
      NoSelfMessage s').
Proof. split_top; [ init_part | intros; next_step; apply StepNoSelfMessage in Hn; eauto ]. Qed.

Theorem SpecLastMessagesGameoverDisconnect :
   (∀ bags H, LastMessagesGameoverDisconnect (Init bags H))
 ∧ (∀ [pl e s s']
      (H1 : LastMessagesGameoverDisconnect s)
      (H2 : MessageSound s)
      (H3 : NoSelfMessage s)
      (H4 : Next pl e s = Some s'),
      LastMessagesGameoverDisconnect s').
Proof. split_top; [ init_part | intros; next_step; apply StepLastMessagesGameoverDisconnect in Hn; eauto ]. Qed.

Theorem SpecTargetNotSelf :
   (∀ bags H, PlayerCount > 1 → NoWinner (Init bags H) → ∀ pl, target (Init bags H) pl ≠ pl)
 ∧ (∀ [pl1 e s s']
      (H1 : PlayerCount > 1 → NoWinner s → ∀ pl, target s pl ≠ pl)
      (H2 : ViewSound s)
      (H2' : MessageSound s)
      (H3 : Next pl1 e s = Some s'),
      PlayerCount > 1 → NoWinner s' → ∀ pl, target s' pl ≠ pl).
Proof.
  split_top; [ init_part | intros pl1 e s s' H1 H2 H2' H3 Hpc Hw ]; next_step.
  assert (Ht0 : TargetNotSelf s0) by auto; unfold TargetNotSelf in Ht0.
  apply StepTargetNotSelf with (pl := pl1) (s := s0); auto.
Qed.

Theorem SpecTargetPlaying :
   (∀ bags H, PlayerCount > 1 → NoWinner (Init bags H) →
      ∀ pl, PlayingView (Init bags H) pl (target (Init bags H) pl) = true)
 ∧ (∀ [pl1 e s s']
      (H1 : PlayerCount > 1 → NoWinner s → ∀ pl, PlayingView s pl (target s pl) = true)
      (HTNS : PlayerCount > 1 → NoWinner s → ∀ pl, target s pl ≠ pl)
      (H2 : ViewSound s)
      (H2' : MessageSound s)
      (H3 : Next pl1 e s = Some s'),
      PlayerCount > 1 → NoWinner s' → ∀ pl, PlayingView s' pl (target s' pl) = true).
Proof.
  split_top; [ init_part | intros pl1 e s s' H1 HTNS H2 H2' H3 Hpc Hw ]; next_step.
  assert (HT : PlayerCount > 1 → NoWinner s0 → Targets s0)
    by (apply TargetsIff; split_top; auto).
  intros pl; apply TargetsPlaying, StepTargets with (pl := pl1) (s := s0); auto.
Qed.

Theorem SpecCorrect :
   (∀ bags H, Correct (Init bags H))
 ∧ (∀ [pl e s s']
      (H1 : Correct s)
      (H2 : Next pl e s = Some s'),
      Correct s').
Proof. split_top; eauto using InitCorrect, NextCorrect. Qed.


(* ========================================================================= *)
(* Step invariants                                                           *)
(* ========================================================================= *)

Theorem GameoverMonotoneHolds : ∀ s s', GameoverMonotone s s'.
Proof.
  intros s s' e pl1 pl2 Hn Hg; apply NextStep in Hn as (s0 & Hs0 & Hn).
  assert (Hg0 : gameover s0 pl2 = true)
    by (decompose [or] Hs0; subst; rewrite ?NewPieceYXStateGameover; assumption).
  eapp StepGameoverMonotone.
Qed.

Theorem DisconnectedMonotoneHolds : ∀ s s', DisconnectedMonotone s s'.
Proof.
  intros s s' e pl1 pl2 Hn Hc; apply NextStep in Hn as (s0 & Hs0 & Hn).
  assert (Hc0 : connected s0 pl2 = false) by (decompose [or] Hs0; subst; assumption).
  eapp StepDisconnectedMonotone.
Qed.

Theorem OtherS6UnchangedHolds : ∀ s s', OtherS6Unchanged s s'.
Proof.
  intros s s' e pl1 pl2 Hn Hne; apply NextStep in Hn as (s0 & Hs0 & Hn).
  assert (E0 : s6 s0 pl2 = s6 s pl2)
    by (decompose [or] Hs0; subst; first [ reflexivity | apply NewPieceYXStateOtherS6; assumption ]).
  rewrite <- E0; eapp StepOtherS6Unchanged.
Qed.

Theorem GameoverViewMonotoneHolds : ∀ s s'
  (Ha : SelfViewAccurate s),
  GameoverViewMonotone s s'.
Proof.
  intros s s' Ha e pl1 pl2 pl3 Hn Hg; apply NextStep in Hn as (s0 & Hs0 & Hn).
  assert (Ha0 : SelfViewAccurate s0) by (apply PreStepInvariants in Hs0; tauto).
  assert (Hg0 : gameoverView s0 pl2 pl3 = true) by (decompose [or] Hs0; subst; assumption).
  eapp StepGameoverViewMonotone.
Qed.

Theorem DisconnectedViewMonotoneHolds : ∀ s s', DisconnectedViewMonotone s s'.
Proof.
  intros s s' e pl1 pl2 pl3 Hn Hc; apply NextStep in Hn as (s0 & Hs0 & Hn).
  assert (Hc0 : connectedView s0 pl2 pl3 = false) by (decompose [or] Hs0; subst; assumption).
  eapp StepDisconnectedViewMonotone.
Qed.

(* The T6 step invariants need only T6.CorrectWithoutGameover, which S6Correct
 * provides (T7 weakens the gameover invariant, see T7.Gameover). *)
Theorem CorrectStepHolds : ∀ pl s s'
  (Hc : Correct s),
  CorrectStep pl s s'.
Proof.
  intros.
  assert (HS : S6Correct s) by (unfold Correct in Hc; tauto).
  assert (HC6 : T6.CorrectWithoutGameover (s6 s pl)) by (specialize (HS pl); tauto).
  assert (Ha : SelfViewAccurate s) by (unfold Correct in Hc; tauto).
  unfold CorrectStep; split_top;
    first [ eapp T5P.StepCorrectWithoutGameover | apply OtherS6UnchangedHolds
          | apply GameoverMonotoneHolds | eapp GameoverViewMonotoneHolds
          | apply DisconnectedMonotoneHolds | apply DisconnectedViewMonotoneHolds ].
Qed.
