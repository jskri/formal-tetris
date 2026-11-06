From Tetris Require Import T3 Notations.
From Tetris Require T1 T2 T2Proofs.
Import T1(Piece, ForbiddenGrid).
Import (notations) T1.
Import T2(s1).

Open Scope nat_scope.

Module T2P := T2Proofs.

(* ========================================================================= *)
(* Helpers                                                                   *)
(* ========================================================================= *)

(* The piece that becomes current when holding: the held one if the slot is not
 * empty (req-hold-swap), the new one otherwise (req-hold-empty). *)
Definition HeldOrNew (pNew : Piece) (s : State) : Piece :=
  match hold s with
  | Some p_held => p_held
  | None => pNew
  end.

(* The T2 part after holding: only the current piece changes. *)
Definition HoldS2 (pNew : Piece) (s : State) : T2.State :=
  T2.UnchangedT2Part (s2 s) (T1.NewPieceState (HeldOrNew pNew s) (s1 (s2 s))).


(* ========================================================================= *)
(* Events: what they change                                                  *)
(* ========================================================================= *)

(* Move and Rotate update the T2 part only, through UnchangedT3Part. *)
Lemma UnchangedT3PartStep : ∀ [o s s']
  (Hn : option_map (UnchangedT3Part s) o = Some s'),
    o = Some (s2 s')
  ∧ hold s' = hold s
  ∧ swapped s' = swapped s.
Proof.
  intros [t |] s s' Hn; [ inject Hn; subst; now split_top | discriminate Hn ].
Qed.

Lemma MovePieceStep : ∀ [s s' dyx]
  (Hn : MovePiece dyx s = Some s'),
    T2.MovePiece dyx (s2 s) = Some (s2 s')
  ∧ hold s' = hold s
  ∧ swapped s' = swapped s.
Proof. intros; exact (UnchangedT3PartStep Hn). Qed.

Lemma RotatePieceStep : ∀ [s s' cw]
  (Hn : RotatePiece cw s = Some s'),
    T2.RotatePiece cw (s2 s) = Some (s2 s')
  ∧ hold s' = hold s
  ∧ swapped s' = swapped s.
Proof. intros; exact (UnchangedT3PartStep Hn). Qed.

Lemma FixPieceStep : ∀ [s s' pNew]
  (Hn : FixPiece pNew s = Some s'),
    T2.FixPiece pNew (s2 s) = Some (s2 s')
  ∧ hold s' = hold s
  ∧ swapped s' = false.
Proof.
  intros s s' pNew Hn; unfold FixPiece in Hn.
  destruct T2.FixPiece; [ inject Hn; subst; now split_top | discriminate Hn ].
Qed.

Lemma HoldPieceStep : ∀ [s s' pNew]
  (Hn : HoldPiece pNew s = Some s'),
    gameover s = false
  ∧ swapped s = false
  ∧ s2 s' = HoldS2 pNew s
  ∧ hold s' = Some (p s)
  ∧ swapped s' = true.
Proof.
  intros s s' pNew Hn; unfold HoldPiece in Hn.
  destruct (gameover s), (swapped s); cbn [negb andb] in Hn; try discriminate Hn.
  inject Hn; subst; now split_top.
Qed.

(* A successful MovePiece proves T2's own guard held. *)
Lemma MovePieceNotGameover : ∀ [s s' dyx]
  (H1 : MovePiece dyx s = Some s'),
  gameover s = false.
Proof.
  intros.
  assert (E2 : T2.MovePiece dyx (s2 s) = Some (s2 s'))
    by (apply MovePieceStep in H1; tauto).
  eapp T2P.MovePieceNotGameover.
Qed.

(* A successful RotatePiece proves T2's own guard held. *)
Lemma RotatePieceNotGameover : ∀ [s s' cw]
  (H1 : RotatePiece cw s = Some s'),
  gameover s = false.
Proof.
  intros.
  assert (E2 : T2.RotatePiece cw (s2 s) = Some (s2 s'))
    by (apply RotatePieceStep in H1; tauto).
  eapp T2P.RotatePieceNotGameover.
Qed.

(**** Move, Rotate and Hold leave mg and gameover unchanged ****)

Lemma MovePieceMgGameoverUnchanged : ∀ [s s' dyx]
  (Hn : MovePiece dyx s = Some s'),
  mg s' = mg s ∧ gameover s' = gameover s.
Proof.
  intros.
  assert (E2 : T2.MovePiece dyx (s2 s) = Some (s2 s'))
    by (apply MovePieceStep in Hn; tauto).
  exact (T2P.MovePieceMgGameoverUnchanged E2).
Qed.

Lemma RotatePieceMgGameoverUnchanged : ∀ [s s' cw]
  (Hn : RotatePiece cw s = Some s'),
  mg s' = mg s ∧ gameover s' = gameover s.
Proof.
  intros.
  assert (E2 : T2.RotatePiece cw (s2 s) = Some (s2 s'))
    by (apply RotatePieceStep in Hn; tauto).
  exact (T2P.RotatePieceMgGameoverUnchanged E2).
Qed.

(* T1.NewPieceState copies mg and gameover. *)
Lemma HoldPieceMgGameoverUnchanged : ∀ [pNew s s']
  (Hn : HoldPiece pNew s = Some s'),
  mg s' = mg s ∧ gameover s' = gameover s.
Proof.
  intros.
  assert (E2 : s2 s' = HoldS2 pNew s) by (apply HoldPieceStep in Hn; tauto).
  unfold mg, gameover; rewrite E2; split_top; reflexivity.
Qed.

Lemma MovePieceGameover : ∀ [s s' dyx]
  (Hn : MovePiece dyx s = Some s'),
  gameover s' = gameover s.
Proof. intros; apply MovePieceMgGameoverUnchanged in Hn; tauto. Qed.

Lemma RotatePieceGameover : ∀ [s s' cw]
  (Hn : RotatePiece cw s = Some s'),
  gameover s' = gameover s.
Proof. intros; apply RotatePieceMgGameoverUnchanged in Hn; tauto. Qed.

Lemma MovePieceMgUnchanged : ∀ [s s' dyx]
  (Hn : MovePiece dyx s = Some s'),
  mg s' = mg s.
Proof. intros; apply MovePieceMgGameoverUnchanged in Hn; tauto. Qed.

Lemma RotatePieceMgUnchanged : ∀ [s s' cw]
  (Hn : RotatePiece cw s = Some s'),
  mg s' = mg s.
Proof. intros; apply RotatePieceMgGameoverUnchanged in Hn; tauto. Qed.

(* Replaces every Move, Rotate, Fix or Hold step hypothesis by the facts the
 * lemmas above provide, one hypothesis per fact. *)
Ltac step_facts :=
  repeat match goal with
  | Hm : MovePiece _ _ = Some _ |- _ =>
      pose proof (MovePieceMgGameoverUnchanged Hm); apply MovePieceStep in Hm
  | Hm : RotatePiece _ _ = Some _ |- _ =>
      pose proof (RotatePieceMgGameoverUnchanged Hm); apply RotatePieceStep in Hm
  | Hm : FixPiece _ _ = Some _ |- _ => apply FixPieceStep in Hm
  | Hm : HoldPiece _ _ = Some _ |- _ =>
      pose proof (HoldPieceMgGameoverUnchanged Hm); apply HoldPieceStep in Hm
  | H : _ ∧ _ |- _ => destruct H
  end.

(* A fall step is a move down or, if that fails, a fix. *)
Lemma FallStepCases : ∀ [s s' pNew]
  (Hn : FallStep pNew s = Some s'),
    MovePiece (-1, 0)%Z s = Some s'
  ∨ (MovePiece (-1, 0)%Z s = None ∧ FixPiece pNew s = Some s').
Proof.
  intros; unfold FallStep in Hn.
  destruct MovePiece eqn: Hm; [ inject Hn; subst | ]; tauto.
Qed.

(* T2's fall step takes the same branch: T3's move down is T2's one, mapped. *)
Lemma FallStepT2 : ∀ [s s' pNew]
  (Hn : FallStep pNew s = Some s'),
  T2.FallStep pNew (s2 s) = Some (s2 s').
Proof.
  intros; unfold FallStep, MovePiece, T2.FallStep in *.
  destruct T2.MovePiece; cbn [option_map] in Hn;
    [ inject Hn; subst; reflexivity | apply FixPieceStep in Hn; tauto ].
Qed.

(* The T2 part of a T2-event step is the T2 step itself. *)
Lemma NextT2EventT2 : ∀ [e2 s s']
  (Hn : NextT2Event e2 s = Some s'),
  T2.Next e2 (s2 s) = Some (s2 s').
Proof.
  intros; destruct e2; cbn [NextT2Event T2.Next] in *;
    first [ eapp FallStepT2 | inject Hn; subst; reflexivity | step_facts; assumption ].
Qed.

(* Every successful step is a move, a rotation, a fix, a hold or a stutter. *)
Lemma NextCases : ∀ [e s s']
  (Hn : Next e s = Some s'),
    (∃ dyx, MovePiece dyx s = Some s')
  ∨ (∃ cw, RotatePiece cw s = Some s')
  ∨ (∃ pNew, FixPiece pNew s = Some s')
  ∨ (∃ pNew, HoldPiece pNew s = Some s')
  ∨ s' = s.
Proof.
  intros; destruct e as [[] |]; cbn [Next NextT2Event] in Hn;
    try (decompose [or and] (FallStepCases Hn); clear Hn);
    try (inject Hn; subst);
    eauto 7.
Qed.


(* ========================================================================= *)
(* State invariants                                                          *)
(* ========================================================================= *)

(**** The T3 part only reads hold, swapped and gameover ****)

(* It carries over when they are unchanged (Move, Rotate), ... *)
Lemma T3InvariantsUnchanged : ∀ [s s']
  (Eh : hold s' = hold s)
  (Esw : swapped s' = swapped s)
  (Ego : gameover s' = gameover s)
  (HS : SwappedImplyHoldSome s)
  (HG : GameoverImplyNotSwapped s),
  SwappedImplyHoldSome s' ∧ GameoverImplyNotSwapped s'.
Proof.
  intros; unfold SwappedImplyHoldSome, GameoverImplyNotSwapped in *.
  rewrite Eh, Esw, Ego; split_top; assumption.
Qed.

(* ... holds vacuously when nothing is swapped (Init, and Fix, which re-enables
 * holding whether or not it triggered a gameover), ... *)
Lemma T3InvariantsNotSwapped : ∀ [s]
  (Esw : swapped s = false),
  SwappedImplyHoldSome s ∧ GameoverImplyNotSwapped s.
Proof.
  intros; unfold SwappedImplyHoldSome, GameoverImplyNotSwapped.
  rewrite Esw; split_top; easy.
Qed.

(* ... and holds after Hold, which fills the slot (req-hold), requires
 * ¬gameover and does not change it. *)
Lemma T3InvariantsHeld : ∀ [s s' q]
  (Eh : hold s' = Some q)
  (Ego : gameover s' = gameover s)
  (Hgo : gameover s = false),
  SwappedImplyHoldSome s' ∧ GameoverImplyNotSwapped s'.
Proof.
  intros; unfold SwappedImplyHoldSome, GameoverImplyNotSwapped.
  rewrite Eh, Ego, Hgo; split_top; easy.
Qed.

Lemma NextT3Invariants : ∀ [e s s']
  (HS : SwappedImplyHoldSome s)
  (HG : GameoverImplyNotSwapped s)
  (Hn : Next e s = Some s'),
  SwappedImplyHoldSome s' ∧ GameoverImplyNotSwapped s'.
Proof.
  intros; decompose [or ex] (NextCases Hn); subst; step_facts;
    first [ split_top; assumption
          | eapp T3InvariantsUnchanged
          | eapp T3InvariantsNotSwapped
          | eapp T3InvariantsHeld ].
Qed.

Lemma InitCorrect : ∀ p : Piece, Correct (Init p).
Proof.
  intros.
  assert (HC2 : T2.Correct (s2 (Init p))) by apply T2P.InitCorrect.
  assert (HI : SwappedImplyHoldSome (Init p) ∧ GameoverImplyNotSwapped (Init p))
    by (apply T3InvariantsNotSwapped; reflexivity).
  unfold Correct; split_top; tauto.
Qed.

(**** CorrectWithoutGameover: the T2 part transfers, then the T3 part ****)

Lemma LiftCorrectWithoutGameover : ∀ [e s s']
  (Hc : CorrectWithoutGameover s)
  (Hn : Next e s = Some s')
  (HC2' : T2.CorrectWithoutGameover (s2 s')),
  CorrectWithoutGameover s'.
Proof.
  intros.
  assert (HS : SwappedImplyHoldSome s)
    by (unfold CorrectWithoutGameover in Hc; tauto).
  assert (HG : GameoverImplyNotSwapped s)
    by (unfold CorrectWithoutGameover in Hc; tauto).
  assert (HI' : SwappedImplyHoldSome s' ∧ GameoverImplyNotSwapped s')
    by eapp NextT3Invariants.
  unfold CorrectWithoutGameover; split_top; tauto.
Qed.

Lemma MovePieceCorrectWithoutGameover : ∀ [dyx s s']
  (Hc : CorrectWithoutGameover s)
  (Hn : MovePiece dyx s = Some s'),
  CorrectWithoutGameover s'.
Proof.
  intros.
  assert (HC2 : T2.CorrectWithoutGameover (s2 s))
    by (unfold CorrectWithoutGameover in Hc; tauto).
  assert (E2 : T2.MovePiece dyx (s2 s) = Some (s2 s'))
    by (apply MovePieceStep in Hn; tauto).
  assert (HC2' : T2.CorrectWithoutGameover (s2 s'))
    by eapp T2P.MovePieceCorrectWithoutGameover.
  eapp (LiftCorrectWithoutGameover (e := Event2 (T2.Move dyx))).
Qed.

Lemma RotatePieceCorrectWithoutGameover : ∀ [cw s s']
  (Hc : CorrectWithoutGameover s)
  (Hn : RotatePiece cw s = Some s'),
  CorrectWithoutGameover s'.
Proof.
  intros.
  assert (HC2 : T2.CorrectWithoutGameover (s2 s))
    by (unfold CorrectWithoutGameover in Hc; tauto).
  assert (E2 : T2.RotatePiece cw (s2 s) = Some (s2 s'))
    by (apply RotatePieceStep in Hn; tauto).
  assert (HC2' : T2.CorrectWithoutGameover (s2 s'))
    by eapp T2P.RotatePieceCorrectWithoutGameover.
  eapp (LiftCorrectWithoutGameover (e := Event2 (T2.Rotate cw))).
Qed.

Lemma FixPieceCorrectWithoutGameover : ∀ [pNew s s']
  (Hc : CorrectWithoutGameover s)
  (Hn : FixPiece pNew s = Some s'),
  CorrectWithoutGameover s'.
Proof.
  intros.
  assert (HC2 : T2.CorrectWithoutGameover (s2 s))
    by (unfold CorrectWithoutGameover in Hc; tauto).
  assert (E2 : T2.FixPiece pNew (s2 s) = Some (s2 s'))
    by (apply FixPieceStep in Hn; tauto).
  assert (HC2' : T2.CorrectWithoutGameover (s2 s'))
    by eapp T2P.FixPieceCorrectWithoutGameover.
  eapp (LiftCorrectWithoutGameover (e := Event2 (T2.Fix pNew))).
Qed.

(* Hold spawns a new current piece, so the T2 part needs the weak gameover fact
 * of T2P.NewPieceStateCorrectWithoutGameover. *)
Lemma HoldPieceCorrectWithoutGameover : ∀ [pNew s s']
  (Hc : CorrectWithoutGameover s)
  (Hg : ForbiddenGrid ∩ T1.mg (T2.s1 (s2 s)) ⊈ ∅ = true → T1.gameover (T2.s1 (s2 s)) = true)
  (Hn : HoldPiece pNew s = Some s'),
  CorrectWithoutGameover s'.
Proof.
  intros.
  assert (HC2 : T2.CorrectWithoutGameover (s2 s))
    by (unfold CorrectWithoutGameover in Hc; tauto).
  assert (E2 : s2 s' = HoldS2 pNew s) by (apply HoldPieceStep in Hn; tauto).
  assert (HC2' : T2.CorrectWithoutGameover (s2 s'))
    by (rewrite E2; apply T2P.NewPieceStateCorrectWithoutGameover; assumption).
  eapp (LiftCorrectWithoutGameover (e := Hold pNew)).
Qed.

(**** Correct: same structure ****)

Lemma NextCorrect : ∀ [e s s']
  (Hc : Correct s)
  (Hn : Next e s = Some s'),
  Correct s'.
Proof.
  intros.
  assert (HC2 : T2.Correct (s2 s)) by (unfold Correct in Hc; tauto).
  assert (HS : SwappedImplyHoldSome s) by (unfold Correct in Hc; tauto).
  assert (HG : GameoverImplyNotSwapped s) by (unfold Correct in Hc; tauto).
  (* T2 events are T2 steps on the T2 part; Hold only gives it a new current
   * piece. *)
  assert (HC2' : T2.Correct (s2 s')). {
    destruct e; cbn [Next] in Hn;
      match goal with
      | Hm : NextT2Event _ _ = Some _ |- _ =>
          apply NextT2EventT2 in Hm; eapp T2P.NextCorrect
      | Hm : HoldPiece ?pNew _ = Some _ |- _ =>
          assert (E2 : s2 s' = HoldS2 pNew s) by (apply HoldPieceStep in Hm; tauto);
          rewrite E2; apply T2P.NewPieceStateCorrect; assumption
      end.
  }
  assert (HI' : SwappedImplyHoldSome s' ∧ GameoverImplyNotSwapped s')
    by eapp NextT3Invariants.
  unfold Correct; split_top; tauto.
Qed.

Theorem SpecCorrect : ∀ e s s',
    (∀ p, Correct (Init p))
  ∧ (Correct s → Next e s = Some s' → Correct s').
Proof. split_top; eauto using InitCorrect, NextCorrect. Qed.


(* ========================================================================= *)
(* Step invariants                                                           *)
(* ========================================================================= *)

(* hold is unchanged by every event but Hold, which fills it. *)
Theorem StepHoldMonotone (s s' : State) :
  HoldMonotone s s'.
Proof.
  intros e Hh Hn.
  decompose [or ex] (NextCases Hn); subst; step_facts; congruence.
Qed.

Theorem CorrectStepHold : ∀ [s] s'
  (Hc : Correct s),
  CorrectStep s s'.
Proof.
  intros.
  assert (HC2 : T2.Correct (s2 s)) by (unfold Correct in Hc; tauto).
  unfold CorrectStep; split_top; auto using T2P.CorrectStepHold, StepHoldMonotone.
Qed.

Theorem CorrectStepHoldWithoutGameover : ∀ [s] s'
  (Hc : CorrectWithoutGameover s),
  CorrectStep s s'.
Proof.
  intros.
  assert (HC2 : T2.CorrectWithoutGameover (s2 s)) by (unfold CorrectWithoutGameover in Hc; tauto).
  unfold CorrectStep; split_top; auto using T2P.CorrectStepHoldWithoutGameover, StepHoldMonotone.
Qed.


(* ========================================================================= *)
(* Refinement                                                                *)
(* ========================================================================= *)

(***************)
(* T3RefinesT2 *)
(***************)

Lemma InitRefine : ∀ p, fₛ (Init p) = T2.Init p.
Proof. reflexivity. Qed.

(*
         e2
   s2    →    s2'
fₛ ↑     ⇑fₑ  ↑ fₛ
   s3    →    s3'
         e2
*)

Lemma NextRefine : ∀ [s3 s3' e2]
  (Hn : Next (Event2 e2) s3 = Some s3'),
  T2.Next (fₑ e2) (fₛ s3) = Some (fₛ s3').
Proof. intros; exact (NextT2EventT2 Hn). Qed.

(* Conversely, a T2 event fails at T3 only when it fails at T2: both steps are
 * guarded by the same T2 step functions. *)
Lemma FallStepNone : ∀ [s pNew]
  (Hn : FallStep pNew s = None),
  T2.FallStep pNew (s2 s) = None.
Proof.
  intros; unfold FallStep, T2.FallStep in *.
  destruct MovePiece eqn: Hm in Hn; [ discriminate Hn | ].
  rewrite (T2P.OptionMapNone Hm); exact (T2P.OptionMapNone Hn).
Qed.

Lemma NextRefineNone : ∀ [s3 e2]
  (Hn : NextT2Event e2 s3 = None),
  T2.Next (fₑ e2) (fₛ s3) = None.
Proof.
  intros; destruct e2; unfold fₛ; cbn [NextT2Event T2.Next fₑ id] in *;
    first [ discriminate Hn | exact (T2P.OptionMapNone Hn) | eapp FallStepNone ].
Qed.

Theorem SpecRefine : T3RefinesT2.
Proof. unfold T3RefinesT2; split_top; eauto using InitRefine, NextRefine. Qed.


(*****************)
(* T3AllowsAllT2 *)
(*****************)

(*
               es2
   T2.Init p   →      s2'
fₛ ↑           ⇓ id   ↑ fₛ
   T3.Init p   →      s3'
               es2
*)

Lemma StepLifts :
  ∀ [e2 s2 s2' s3]
    (H1 : fₛ s3 = s2)
    (H2 : T2.Next e2 s2 = Some s2'),
    ∃ s3', NextT2Event e2 s3 = Some s3' ∧ fₛ s3' = s2'.
Proof.
  intros.
  destruct (NextT2Event e2 s3) as [s3' |] eqn: Hn.
  - assert (Hfs : fₛ s3' = s2')
      by (apply NextRefine in Hn; cbv [fₑ id] in Hn; rewrite H1, H2 in Hn; congruence).
    exists s3'; split_top; (reflexivity || assumption).
  - apply NextRefineNone in Hn; cbv [fₑ id] in Hn; rewrite H1, H2 in Hn.
    discriminate Hn.
Qed.

(* Generalized over the starting states, so that the induction hypothesis
 * applies at every point along the run. *)
Lemma RunLifts : ∀ es2 s2 s2' s3
  (Hfs : fₛ s3 = s2)
  (Hrun : RunT2 es2 s2 = Some s2'),
  ∃ s3', RunT3 es2 s3 = Some s3' ∧ fₛ s3' = s2'.
Proof.
  induction es2 as [| e2 es2 IH]; intros; cbn [RunT2 RunT3] in Hrun |- *.
  - exists s3; split_top; congruence.
  - destruct (T2.Next e2 s2) as [s2'' |] eqn: Hstep; [ | discriminate Hrun ].
    (* the T2 step lifts to a T3 step from s3, then the induction hypothesis
     * lifts the rest of the run *)
    apply StepLifts with (s3 := s3) in Hstep; [ | assumption ].
    destruct Hstep as (s3'' & Hstep).
    assert (Hn : NextT2Event e2 s3 = Some s3'') by tauto.
    assert (Hfs'' : fₛ s3'' = s2'') by tauto.
    rewrite Hn; eapp IH.
Qed.

Theorem T3AllowsAllT2Hold : T3AllowsAllT2.
Proof.
  intros p es2 s2' H1.
  assert (HI : fₛ (Init p) = T2.Init p) by apply InitRefine.
  apply RunLifts with (s3 := Init p) in H1; [ | assumption ].
  destruct H1 as (s3' & H1); exists s3'; split_top; tauto.
Qed.
