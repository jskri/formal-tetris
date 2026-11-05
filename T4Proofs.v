From Tetris Require Import T4 Notations.
From Tetris Require T1 T2 T3 T3Proofs.
From Stdlib Require Import Lia PeanoNat.
Import T1(Piece, ForbiddenGrid).
Import (notations) T1.

Open Scope nat_scope.

Module T3P := T3Proofs.

(* ========================================================================= *)
(* The Draw                                                                  *)
(* ========================================================================= *)

(* Everything that is specific to T4 happens here. *)

(* The Draw obtained after popping one piece, and the Draw after a hold: the
 * preview is consumed only when the hold slot is empty (req-hold-empty), since
 * otherwise the held piece becomes current (req-hold-swap). *)
Definition DrawAfter (s : State) (bagNew : ℕ → Piece) : Draw :=
  snd (DrawNextPiece (d s) bagNew).

Definition HoldDraw (s : State) (bagNew : ℕ → Piece) : Draw :=
  match hold s with
  | Some _ => d s
  | None => DrawAfter s bagNew
  end.

(* A full bag has fed no preview entry yet, so BagNextConsistentD is vacuous
 * (k = 0). *)
Lemma FullBagCorrectD : ∀ [dd : Draw]
  (HP : PieceSet (bag_ dd))
  (HL : bagLen_ dd = MaxBagLen),
  CorrectD dd.
Proof.
  intros.
  assert (HM : MaxBagLen > 0) by exact AxiomsMaxBagLen.
  unfold CorrectD, BagNextConsistentD; cbv zeta; rewrite HL.
  split_top; first [ assumption | lia | intros; lia ].
Qed.

(* req-preview-pop: drawing preserves the Draw invariant. *)
Lemma DrawNextPieceCorrect : ∀ [dd : Draw] [bagNew : ℕ → Piece]
  (HB : PieceSet bagNew)
  (HD : CorrectD dd),
  CorrectD (snd (DrawNextPiece dd bagNew)).
Proof.
  intros.
  assert (HP : PieceSet (bag_ dd)) by (unfold CorrectD in HD; tauto).
  assert (HL : 0 < bagLen_ dd) by (unfold CorrectD in HD; tauto).
  assert (HC : BagNextConsistentD dd) by (unfold CorrectD in HD; tauto).
  unfold BagNextConsistentD in HC; cbv zeta in HC.
  unfold DrawNextPiece; cbv zeta; cbn [snd].
  destruct (Nat.leb_spec (bagLen_ dd) 1).
  - (* a single piece left: the bag is refilled to MaxBagLen *)
    apply FullBagCorrectD; (reflexivity || assumption).
  - (* at least two pieces: the last one is popped onto the end of the
     * preview, and every other preview entry shifts down by one *)
    assert (L3 : ∀ i, i < min (MaxBagLen - (bagLen_ dd - 1)) NextLen →
        ShiftNext (next_ dd) (bag_ dd (bagLen_ dd - 1)) (NextLen - i - 1)
      = bag_ dd (bagLen_ dd - 1 + i)). {
      intros i Hi; unfold ShiftNext.
      destruct (Nat.eqb_spec (NextLen - i - 1) (NextLen - 1)) as [Ei | Ei].
      - (* i = 0: the popped piece lands at the end of the preview *)
        f_equal; lia.
      - (* i = S i': the preview entry the old one shifts down from *)
        destruct i as [| i']; [ lia | ].
        replace (NextLen - S i' - 1 + 1) with (NextLen - i' - 1) by lia.
        replace (bagLen_ dd - 1 + S i') with (bagLen_ dd + i') by lia.
        apply HC; lia.
    }
    unfold CorrectD, BagNextConsistentD; cbv zeta; cbn [bag_ bagLen_ next_].
    split_top; first [ assumption | lia ].
Qed.

Lemma DrawAfterCorrect : ∀ [s bagNew]
  (HB : PieceSet bagNew)
  (HD : CorrectD (d s)),
  CorrectD (DrawAfter s bagNew).
Proof. intros; eapp DrawNextPieceCorrect. Qed.

Lemma HoldDrawCorrect : ∀ [s bagNew]
  (HB : PieceSet bagNew)
  (HD : CorrectD (d s)),
  CorrectD (HoldDraw s bagNew).
Proof.
  intros; unfold HoldDraw.
  destruct (hold s); first [ assumption | eapp DrawAfterCorrect ].
Qed.

(* Generalized over the starting Draw, so that the induction hypothesis
 * applies after every draw. *)
Lemma BuildInitNextCorrect :
  ∀ (i : ℕ) (bags : ℕ → ℕ → Piece) (bagIdx : ℕ) (dd : Draw)
  (HB : ∀ j, PieceSet (bags j))
  (HD : CorrectD dd),
  CorrectD (fst (BuildInitNext dd i bags bagIdx)).
Proof.
  induction i as [| i IH]; intros; cbn [BuildInitNext].
  - exact HD.
  - apply IH; try apply DrawNextPieceCorrect; auto.
Qed.

(* req-preview-init: the preview is filled from a full bag, then the first
 * piece is drawn. *)
Lemma InitDrawCorrect : ∀ (bags : ℕ → ℕ → Piece) (HB : ∀ i, PieceSet (bags i)),
  CorrectD (snd (InitPieceAndDraw bags HB)).
Proof.
  intros.
  unfold InitPieceAndDraw; cbv zeta.
  (* The seed Draw's `next_` is arbitrary, which is harmless since its bag is
   * full. *)
  set (dd0 := {| bag_ := bags 0; bagLen_ := MaxBagLen; next_ := bags 0 |}).
  assert (HD0 : CorrectD dd0) by (apply FullBagCorrectD; (reflexivity || apply HB)).
  assert (HD1 : CorrectD (fst (BuildInitNext dd0 NextLen bags 1)))
    by auto using BuildInitNextCorrect.
  destruct BuildInitNext; auto using DrawNextPieceCorrect.
Qed.


(* ========================================================================= *)
(* Events: what they do to the two components of the state                   *)
(* ========================================================================= *)

(* FixPiece and HoldPiece destructure `DrawNextPiece (d s) bagNew`, which is a
 * literal pair: the `let` reduces, so both are convertible to a plain option_map
 * over the corresponding T3 event applied to the popped piece `next s 0`. *)

Lemma FixPieceEq : ∀ (s : State) (bagNew : ℕ → Piece) (H : PieceSet bagNew),
  FixPiece bagNew H s
  = option_map (λ t, mkState t (DrawAfter s bagNew)) (T3.FixPiece (next s 0) (s3 s)).
Proof. reflexivity. Qed.

Lemma HoldPieceEq : ∀ (s : State) (bagNew : ℕ → Piece) (H : PieceSet bagNew),
  HoldPiece bagNew H s
  = if ! gameover s
    then option_map (λ t, mkState t (HoldDraw s bagNew)) (T3.HoldPiece (next s 0) (s3 s))
    else None.
Proof. reflexivity. Qed.

(* Move and Rotate update the T3 part only, through UnchangedT4Part. *)
Lemma UnchangedT4PartStep : ∀ [o s s']
  (Hn : option_map (UnchangedT4Part s) o = Some s'),
  o = Some (s3 s') ∧ d s' = d s.
Proof.
  intros [t |] s s' Hn; [ inject Hn; subst; now split_top | discriminate Hn ].
Qed.

Lemma MovePieceStep : ∀ [s s' dyx]
  (Hn : MovePiece dyx s = Some s'),
  T3.MovePiece dyx (s3 s) = Some (s3 s') ∧ d s' = d s.
Proof. intros; exact (UnchangedT4PartStep Hn). Qed.

Lemma RotatePieceStep : ∀ [s s' cw]
  (Hn : RotatePiece cw s = Some s'),
  T3.RotatePiece cw (s3 s) = Some (s3 s') ∧ d s' = d s.
Proof. intros; exact (UnchangedT4PartStep Hn). Qed.

Lemma MovePieceFail : ∀ [s dyx]
  (Hn : MovePiece dyx s = None),
  T3.MovePiece dyx (s3 s) = None.
Proof.
  intros; unfold MovePiece in Hn.
  destruct T3.MovePiece; [ discriminate Hn | reflexivity ].
Qed.

Lemma FixPieceStep : ∀ [s s' bagNew] [H : PieceSet bagNew]
  (Hn : FixPiece bagNew H s = Some s'),
    T3.FixPiece (next s 0) (s3 s) = Some (s3 s')
  ∧ d s' = DrawAfter s bagNew.
Proof.
  intros; rewrite FixPieceEq in Hn.
  destruct T3.FixPiece; [ inject Hn; subst; now split_top | discriminate Hn ].
Qed.

Lemma HoldPieceStep : ∀ [s s' bagNew] [H : PieceSet bagNew]
  (Hn : HoldPiece bagNew H s = Some s'),
    gameover s = false
  ∧ T3.HoldPiece (next s 0) (s3 s) = Some (s3 s')
  ∧ d s' = HoldDraw s bagNew.
Proof.
  intros; rewrite HoldPieceEq in Hn.
  destruct (gameover s); cbn [negb] in Hn; try discriminate Hn.
  destruct T3.HoldPiece; [ inject Hn; subst; now split_top | discriminate Hn ].
Qed.

(* Replaces every Move, Rotate, Fix or Hold step hypothesis, and every failed
 * move, by the facts the lemmas above provide, one hypothesis per fact. *)
Ltac step_facts :=
  repeat match goal with
  | Hm : MovePiece _ _ = Some _ |- _ => apply MovePieceStep in Hm
  | Hm : MovePiece _ _ = None |- _ => apply MovePieceFail in Hm
  | Hm : RotatePiece _ _ = Some _ |- _ => apply RotatePieceStep in Hm
  | Hm : FixPiece _ _ _ = Some _ |- _ => apply FixPieceStep in Hm
  | Hm : HoldPiece _ _ _ = Some _ |- _ => apply HoldPieceStep in Hm
  | H : _ ∧ _ |- _ => destruct H
  end.

(* A fall step is a move down or, if that fails, a fix. *)
Lemma FallStepCases : ∀ [s s' bagNew] [H : PieceSet bagNew]
  (Hn : FallStep bagNew H s = Some s'),
    MovePiece (-1, 0)%Z s = Some s'
  ∨ (MovePiece (-1, 0)%Z s = None ∧ FixPiece bagNew H s = Some s').
Proof.
  intros; unfold FallStep in Hn.
  destruct MovePiece eqn: Hm; [ inject Hn; subst | ]; tauto.
Qed.

(* T3's fall step takes the same branch: T4's move down is T3's one, mapped. *)
Lemma FallStepT3 : ∀ [s s' bagNew] [H : PieceSet bagNew]
  (Hn : FallStep bagNew H s = Some s'),
  T3.FallStep (next s 0) (s3 s) = Some (s3 s').
Proof.
  intros; unfold T3.FallStep.
  decompose [or and] (FallStepCases Hn); step_facts;
    match goal with E : T3.MovePiece _ _ = _ |- _ => rewrite E end;
    (reflexivity || assumption).
Qed.

(* The T3 part of a step is the T3 step of the mapped event. *)
Lemma NextT3 : ∀ [e s s']
  (Hn : Next e s = Some s'),
  T3.Next (fₑ s e) (s3 s) = Some (s3 s').
Proof.
  intros; destruct e; cbn [Next T3.Next T3.NextT2Event fₑ] in *;
    first [ eapp FallStepT3 | inject Hn; subst; reflexivity | step_facts; assumption ].
Qed.

(* Every successful step is a move, a rotation, a fix, a hold or a stutter. *)
Lemma NextCases : ∀ [e s s']
  (Hn : Next e s = Some s'),
    (∃ dyx, MovePiece dyx s = Some s')
  ∨ (∃ cw, RotatePiece cw s = Some s')
  ∨ (∃ bagNew H, FixPiece bagNew H s = Some s')
  ∨ (∃ bagNew H, HoldPiece bagNew H s = Some s')
  ∨ s' = s.
Proof.
  intros; destruct e; cbn [Next] in Hn;
    try (decompose [or and] (FallStepCases Hn); clear Hn);
    try (inject Hn; subst);
    eauto 8.
Qed.

(**** What the T3 lemmas give through the s3 projection ****)

(* A successful MovePiece proves T3's own guard held. *)
Lemma MovePieceNotGameover : ∀ [s s' dyx]
  (H1 : MovePiece dyx s = Some s'),
  gameover s = false.
Proof. intros; step_facts; eapp T3P.MovePieceNotGameover. Qed.

(* A successful RotatePiece proves T3's own guard held. *)
Lemma RotatePieceNotGameover : ∀ [s s' cw]
  (H1 : RotatePiece cw s = Some s'),
  gameover s = false.
Proof. intros; step_facts; eapp T3P.RotatePieceNotGameover. Qed.

Lemma MovePieceMgGameoverUnchanged : ∀ [s s' dyx]
  (Hn : MovePiece dyx s = Some s'),
  mg s' = mg s ∧ gameover s' = gameover s.
Proof. intros; step_facts; eapp T3P.MovePieceMgGameoverUnchanged. Qed.

Lemma RotatePieceMgGameoverUnchanged : ∀ [s s' cw]
  (Hn : RotatePiece cw s = Some s'),
  mg s' = mg s ∧ gameover s' = gameover s.
Proof. intros; step_facts; eapp T3P.RotatePieceMgGameoverUnchanged. Qed.

Lemma HoldPieceMgGameoverUnchanged : ∀ [bagNew] [H : PieceSet bagNew] [s s']
  (Hn : HoldPiece bagNew H s = Some s'),
  mg s' = mg s ∧ gameover s' = gameover s.
Proof. intros; step_facts; eapp T3P.HoldPieceMgGameoverUnchanged. Qed.


(* ========================================================================= *)
(* State invariants                                                          *)
(* ========================================================================= *)

(**** The Draw part ****)

(* The Draw is unchanged (Move, Rotate, Stutter), popped (Fix) or popped only
 * when the hold slot is empty (Hold). *)
Lemma NextCorrectD : ∀ [e s s']
  (HD : CorrectD (d s))
  (Hn : Next e s = Some s'),
  CorrectD (d s').
Proof.
  intros; decompose [or ex] (NextCases Hn); subst; step_facts;
    try match goal with Ed : d _ = _ |- _ => rewrite Ed end;
    first [ assumption | eapp DrawAfterCorrect | eapp HoldDrawCorrect ].
Qed.

Lemma InitCorrect : ∀ (bags : ℕ → ℕ → Piece) (HB : ∀ i, PieceSet (bags i)),
  Correct (Init bags HB).
Proof.
  intros.
  assert (HD : CorrectD (snd (InitPieceAndDraw bags HB))) by apply InitDrawCorrect.
  assert (HC3 : ∀ p, T3.Correct (T3.Init p)) by apply T3P.InitCorrect.
  unfold Init; destruct InitPieceAndDraw as [p0 d0]; cbn [snd] in HD.
  unfold Correct; cbn [s3 d]; split_top; auto.
Qed.

(**** CorrectWithoutGameover: the T3 part transfers, then the Draw part ****)

Lemma LiftCorrectWithoutGameover : ∀ [e s s']
  (Hc : CorrectWithoutGameover s)
  (Hn : Next e s = Some s')
  (HC3' : T3.CorrectWithoutGameover (s3 s')),
  CorrectWithoutGameover s'.
Proof.
  intros.
  assert (HD : CorrectD (d s)) by (unfold CorrectWithoutGameover in Hc; tauto).
  assert (HD' : CorrectD (d s')) by eapp NextCorrectD.
  unfold CorrectWithoutGameover; split_top; assumption.
Qed.

Lemma MovePieceCorrectWithoutGameover : ∀ [dyx s s']
  (Hc : CorrectWithoutGameover s)
  (Hm : MovePiece dyx s = Some s'),
  CorrectWithoutGameover s'.
Proof.
  intros.
  assert (HC3 : T3.CorrectWithoutGameover (s3 s))
    by (unfold CorrectWithoutGameover in Hc; tauto).
  assert (E3 : T3.MovePiece dyx (s3 s) = Some (s3 s'))
    by (apply MovePieceStep in Hm; tauto).
  assert (HC3' : T3.CorrectWithoutGameover (s3 s'))
    by eapp T3P.MovePieceCorrectWithoutGameover.
  eapp (LiftCorrectWithoutGameover (e := Move dyx)).
Qed.

Lemma RotatePieceCorrectWithoutGameover : ∀ [cw s s']
  (Hc : CorrectWithoutGameover s)
  (Hm : RotatePiece cw s = Some s'),
  CorrectWithoutGameover s'.
Proof.
  intros.
  assert (HC3 : T3.CorrectWithoutGameover (s3 s))
    by (unfold CorrectWithoutGameover in Hc; tauto).
  assert (E3 : T3.RotatePiece cw (s3 s) = Some (s3 s'))
    by (apply RotatePieceStep in Hm; tauto).
  assert (HC3' : T3.CorrectWithoutGameover (s3 s'))
    by eapp T3P.RotatePieceCorrectWithoutGameover.
  eapp (LiftCorrectWithoutGameover (e := Rotate cw)).
Qed.

Lemma FixPieceCorrectWithoutGameover : ∀ [bagNew] [H : PieceSet bagNew] [s s']
  (Hc : CorrectWithoutGameover s)
  (Hm : FixPiece bagNew H s = Some s'),
  CorrectWithoutGameover s'.
Proof.
  intros.
  assert (HC3 : T3.CorrectWithoutGameover (s3 s))
    by (unfold CorrectWithoutGameover in Hc; tauto).
  assert (E3 : T3.FixPiece (next s 0) (s3 s) = Some (s3 s'))
    by (apply FixPieceStep in Hm; tauto).
  assert (HC3' : T3.CorrectWithoutGameover (s3 s'))
    by eapp T3P.FixPieceCorrectWithoutGameover.
  eapp (LiftCorrectWithoutGameover (e := Fix bagNew H)).
Qed.

(* Hold's weak gameover fact is T3's, through the s3 projection. *)
Lemma HoldPieceCorrectWithoutGameover : ∀ [bagNew] [H : PieceSet bagNew] [s s']
  (Hc : CorrectWithoutGameover s)
  (Hg : ForbiddenGrid ∩ T1.mg (T2.s1 (T3.s2 (s3 s))) ⊈ ∅ = true
        → T1.gameover (T2.s1 (T3.s2 (s3 s))) = true)
  (Hm : HoldPiece bagNew H s = Some s'),
  CorrectWithoutGameover s'.
Proof.
  intros.
  assert (HC3 : T3.CorrectWithoutGameover (s3 s))
    by (unfold CorrectWithoutGameover in Hc; tauto).
  assert (E3 : T3.HoldPiece (next s 0) (s3 s) = Some (s3 s'))
    by (apply HoldPieceStep in Hm; tauto).
  assert (HC3' : T3.CorrectWithoutGameover (s3 s'))
    by eapp T3P.HoldPieceCorrectWithoutGameover.
  eapp (LiftCorrectWithoutGameover (e := Hold bagNew H)).
Qed.

(**** Correct: the T3 part is a T3 step, the Draw part is NextCorrectD ****)

Lemma NextCorrect : ∀ [e s s']
  (Hc : Correct s)
  (Hn : Next e s = Some s'),
  Correct s'.
Proof.
  intros.
  assert (HC3 : T3.Correct (s3 s)) by (unfold Correct in Hc; tauto).
  assert (HD : CorrectD (d s)) by (unfold Correct in Hc; tauto).
  assert (E3 : T3.Next (fₑ s e) (s3 s) = Some (s3 s')) by eapp NextT3.
  assert (HC3' : T3.Correct (s3 s')) by eapp T3P.NextCorrect.
  assert (HD' : CorrectD (d s')) by eapp NextCorrectD.
  unfold Correct; split_top; assumption.
Qed.

Theorem SpecCorrect : ∀ e s s',
    (∀ bags HB, Correct (Init bags HB))
  ∧ (Correct s → Next e s = Some s' → Correct s').
Proof. split_top; eauto using InitCorrect, NextCorrect. Qed.


(* ========================================================================= *)
(* Step invariants                                                           *)
(* ========================================================================= *)

Theorem CorrectStepHold : ∀ [s] s'
  (Hc : Correct s),
  CorrectStep s s'.
Proof.
  intros.
  assert (HC3 : T3.Correct (s3 s)) by (unfold Correct in Hc; tauto).
  exact (T3P.CorrectStepHold _ HC3).
Qed.


(* ========================================================================= *)
(* Refinement                                                                *)
(* ========================================================================= *)

Lemma InitRefine : ∀ bags HSet,
  fₛ (T4.Init bags HSet) = T3.Init (T4.InitPiece bags HSet).
Proof.
  intros; unfold fₛ, Init, InitPiece.
  destruct InitPieceAndDraw; reflexivity.
Qed.

(*
         e3
   s3    →         s3'
fₛ ↑     ⇑(fₑ s4)  ↑ fₛ
   s4    →         s4'
         e4
*)

Lemma NextRefine : ∀ e4 s4 s4'
  (H1 : T4.Next e4 s4 = Some s4'),
  T3.Next (fₑ s4 e4) (fₛ s4) = Some (s3 s4').
Proof. intros; exact (NextT3 H1). Qed.

Theorem T4RefinesT3Hold : T4RefinesT3.
Proof. unfold T4RefinesT3; split_top; auto using InitRefine, NextRefine. Qed.


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
