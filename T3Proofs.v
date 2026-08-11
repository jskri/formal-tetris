From Tetris Require Import T3 Notations.
From Tetris Require T1 T2 T1Proofs T2Proofs.
From Stdlib Require Import Lia.
Import T1(Piece, ForbiddenGrid).
Import (notations) T1.
Import T2(s1).

Open Scope nat_scope.

Module T1P := T1Proofs.
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

(***************************************************************************
Step lemmas: each event's effect on the two components of the state, i.e. on
the forwarded T2 part and on the T3 part (hold, swapped).
 ***************************************************************************)

Lemma MovePieceStep : ∀ [s s' dyx]
  (Hn : MovePiece dyx s = Some s'),
    T2.MovePiece dyx (s2 s) = Some (s2 s')
  ∧ hold s' = hold s
  ∧ swapped s' = swapped s.
Proof.
  intros s s' dyx Hn.
  unfold MovePiece, option_map in Hn.
  destruct (T2.MovePiece dyx (s2 s)) as [t |] eqn: Hd; try rewrite Hd in Hn.
  - (* only the T2 part changes; UnchangedT3Part copies hold and swapped *)
    assert (L1 : s' = UnchangedT3Part s t) by (inject Hn; now symmetry).
    rewrite L1; unfold UnchangedT3Part; simpl.
    now repeat split.
  - discriminate Hn.
Qed.

Lemma RotatePieceStep : ∀ [s s' cw]
  (Hn : RotatePiece cw s = Some s'),
    T2.RotatePiece cw (s2 s) = Some (s2 s')
  ∧ hold s' = hold s
  ∧ swapped s' = swapped s.
Proof.
  intros s s' cw Hn.
  unfold RotatePiece, option_map in Hn.
  destruct (T2.RotatePiece cw (s2 s)) as [t |] eqn: Hd; try rewrite Hd in Hn.
  - assert (L1 : s' = UnchangedT3Part s t) by (inject Hn; now symmetry).
    rewrite L1; unfold UnchangedT3Part; simpl.
    now repeat split.
  - discriminate Hn.
Qed.

(* A successful MovePiece proves T2's own guard held. *)
Lemma MovePieceNotGameover : ∀ [s s' dyx]
  (H1 : MovePiece dyx s = Some s'),
  gameover s = false.
Proof.
  intros.
  destruct (MovePieceStep H1) as [H2 _].
  exact (T2P.MovePieceNotGameover H2).
Qed.

(* A successful RotatePiece proves T2's own guard held. *)
Lemma RotatePieceNotGameover : ∀ [s s' cw]
  (H1 : RotatePiece cw s = Some s'),
  gameover s = false.
Proof.
  intros.
  destruct (RotatePieceStep H1) as [H2 _].
  exact (T2P.RotatePieceNotGameover H2).
Qed.

Lemma FixPieceStep : ∀ [s s' pNew]
  (Hn : FixPiece pNew s = Some s'),
    T2.FixPiece pNew (s2 s) = Some (s2 s')
  ∧ hold s' = hold s
  ∧ swapped s' = false.
Proof.
  intros s s' pNew Hn.
  unfold FixPiece, option_map in Hn.
  destruct (T2.FixPiece pNew (s2 s)) as [t |] eqn: Hd; try rewrite Hd in Hn.
  - assert (L1 : s' = {| s2 := t; swapped := false; hold := hold s |})
      by (inject Hn; now symmetry).
    rewrite L1; simpl.
    now repeat split.
  - discriminate Hn.
Qed.

Lemma MovePieceFail : ∀ [s dyx]
  (Hn : MovePiece dyx s = None),
  T2.MovePiece dyx (s2 s) = None.
Proof.
  intros s dyx Hn.
  unfold MovePiece, option_map in Hn.
  destruct (T2.MovePiece dyx (s2 s)) eqn: Hd; now try discriminate Hn.
Qed.

Lemma FallStepStep : ∀ [s s' pNew]
  (Hn : FallStep pNew s = Some s'),
    T2.FallStep pNew (s2 s) = Some (s2 s')
  ∧ hold s' = hold s.
Proof.
  intros s s' pNew Hn.
  unfold FallStep in Hn.
  destruct MovePiece as [t |] eqn: Hd in Hn.
  - (* the piece could move down: T2's FallStep takes the same branch *)
    assert (L1 : MovePiece (-1, 0)%Z s = Some s') by (rewrite Hd; exact Hn).
    set (LS := MovePieceStep L1).
    assert (E2 : T2.MovePiece ((-1)%Z, 0%Z) (s2 s) = Some (s2 s'))
      by now destruct LS; tauto.
    assert (Eh : hold s' = hold s) by now destruct LS; tauto.
    unfold T2.FallStep; rewrite E2.
    split; [ reflexivity | exact Eh ].
  - (* the piece could not move down: both fix *)
    assert (L1 : T2.MovePiece (-1, 0)%Z (s2 s) = None) by (apply MovePieceFail; exact Hd).
    set (LS := FixPieceStep Hn).
    assert (E2 : T2.FixPiece pNew (s2 s) = Some (s2 s'))
      by now destruct LS; tauto.
    assert (Eh : hold s' = hold s) by now destruct LS; tauto.
    unfold T2.FallStep; rewrite L1, E2.
    split; [ reflexivity | exact Eh ].
Qed.

Lemma HoldPieceStep : ∀ [s s' pNew]
  (Hn : HoldPiece pNew s = Some s'),
    gameover s = false
  ∧ swapped s = false
  ∧ s2 s' = T2.UnchangedT2Part (s2 s) (T1.NewPieceState (HeldOrNew pNew s) (s1 (s2 s)))
  ∧ hold s' = Some (p s)
  ∧ swapped s' = true.
Proof.
  intros s s' pNew Hn.
  unfold HoldPiece in Hn.
  destruct (! gameover s && ! swapped s) eqn: Hg; [ | discriminate Hn ].
  assert (L1 : gameover s = false ∧ swapped s = false). {
    keep_only Hg.
    apply andb_true_iff in Hg as [H1 H2].
    apply negb_true_iff in H1; apply negb_true_iff in H2.
    split; assumption.
  }
  destruct L1 as [Hgo Hsw].
  cbv zeta in Hn.
  inject Hn.
  rewrite <- Hn; simpl.
  repeat split; (exact Hgo || exact Hsw).
Qed.

Lemma StutterStep : ∀ [s s']
  (Hn : Next (Event2 T2.Stutter) s = Some s'),
  s' = s.
Proof.
  intros s s' Hn.
  now inject Hn.
Qed.

(***************************************************************************
Gameover propagation. Move and Rotate leave `gameover` untouched (their T1
counterparts do), and so does Hold, since T1.NewPieceState copies it.
 ***************************************************************************)

Lemma MovePieceGameover : ∀ [s s' dyx]
  (Hn : MovePiece dyx s = Some s'),
  gameover s' = gameover s.
Proof.
  intros s s' dyx Hn.
  assert (L1 : T2.MovePiece dyx (s2 s) = Some (s2 s'))
    by (apply MovePieceStep in Hn as [H1 _]; exact H1).
  assert (L2 : T1.MovePiece dyx (s1 (s2 s)) = Some (s1 (s2 s'))). {
    keep_only L1.
    apply T2P.MovePieceStep in L1 as [H1 _]; now symmetry.
  }
  keep_only L2.
  assert (L3 : T1.gameover (s1 (s2 s')) = T1.gameover (s1 (s2 s)))
    by now apply T1P.MovePieceUnchanged in L2; tauto.
  exact L3.
Qed.

Lemma RotatePieceGameover : ∀ [s s' cw]
  (Hn : RotatePiece cw s = Some s'),
  gameover s' = gameover s.
Proof.
  intros s s' cw Hn.
  assert (L1 : T2.RotatePiece cw (s2 s) = Some (s2 s'))
    by (apply RotatePieceStep in Hn as [H1 _]; exact H1).
  assert (L2 : T1.RotatePiece cw (s1 (s2 s)) = Some (s1 (s2 s'))). {
    keep_only L1.
    apply T2P.RotatePieceStep in L1 as [H1 _]; now symmetry.
  }
  keep_only L2.
  assert (L3 : T1.gameover (s1 (s2 s')) = T1.gameover (s1 (s2 s)))
    by now apply T1P.RotatePieceOK in L2; tauto.
  exact L3.
Qed.

(* mg-unchanged counterparts to MovePieceGameover/RotatePieceGameover above. *)
Lemma MovePieceMgUnchanged : ∀ [s s' dyx]
  (Hn : MovePiece dyx s = Some s'),
  mg s' = mg s.
Proof.
  intros.
  destruct (MovePieceStep Hn) as [H1 _].
  destruct (T2P.MovePieceMgGameoverUnchanged H1) as [Emg _].
  exact Emg.
Qed.

Lemma RotatePieceMgUnchanged : ∀ [s s' cw]
  (Hn : RotatePiece cw s = Some s'),
  mg s' = mg s.
Proof.
  intros.
  destruct (RotatePieceStep Hn) as [H1 _].
  destruct (T2P.RotatePieceMgGameoverUnchanged H1) as [Emg _].
  exact Emg.
Qed.

(* Hold: T1.NewPieceState leaves mg/gameover unchanged by construction
(reflexivity), and HoldPieceStep already exposes exactly the s2 s' =
UnchangedT2Part ... (NewPieceState ...) equation needed to carry that up. *)
Lemma HoldPieceMgGameoverUnchanged : ∀ [pNew s s']
  (Hn : HoldPiece pNew s = Some s'),
  mg s' = mg s ∧ gameover s' = gameover s.
Proof.
  intros.
  destruct (HoldPieceStep Hn) as (_ & _ & E2 & _ & _).
  assert (Emg : T2.mg (s2 s') = T2.mg (s2 s)) by (rewrite E2; reflexivity).
  assert (Ego : T2.gameover (s2 s') = T2.gameover (s2 s)) by (rewrite E2; reflexivity).
  unfold mg, gameover; split; assumption.
Qed.


(* ========================================================================= *)
(* State invariants                                                          *)
(* ========================================================================= *)

Lemma InitCorrect : ∀ p : Piece, Correct (Init p).
Proof.
  intros p.
  assert (L1 : T2.Correct (s2 (Init p))) by (apply T2P.InitCorrect).
  (* Initially nothing is held, and nothing has been swapped. *)
  assert (L2 : SwappedImplyHoldSome (Init p))
    by (unfold SwappedImplyHoldSome; intros H1; discriminate H1).
  assert (L3 : GameoverImplyNotSwapped (Init p))
    by (unfold GameoverImplyNotSwapped; intros _; reflexivity).
  unfold Correct; split; [ exact L1 | split; assumption ].
Qed.

Lemma MovePieceCorrectWithoutGameover : ∀ [dyx s s']
  (Hc : CorrectWithoutGameover s)
  (Hm : MovePiece dyx s = Some s'),
  CorrectWithoutGameover s'.
Proof.
  intros.
  assert (HC2 : T2.CorrectWithoutGameover (s2 s)) by now destruct Hc; tauto.
  assert (HS : SwappedImplyHoldSome s) by now destruct Hc; tauto.
  assert (HG : GameoverImplyNotSwapped s) by now destruct Hc; tauto.
  set (LS := MovePieceStep Hm).
  assert (E2 : T2.MovePiece dyx (s2 s) = Some (s2 s')) by now destruct LS; tauto.
  assert (Eh : hold s' = hold s) by now destruct LS; tauto.
  assert (Esw : swapped s' = swapped s) by now destruct LS; tauto.
  assert (L1 : T2.CorrectWithoutGameover (s2 s'))
    by (apply (@T2P.MovePieceCorrectWithoutGameover dyx (s2 s) (s2 s') HC2 E2)).
  assert (L2 : SwappedImplyHoldSome s')
    by (unfold SwappedImplyHoldSome; rewrite Eh, Esw; exact HS).
  assert (L3 : GameoverImplyNotSwapped s'). {
    assert (Ego : gameover s' = gameover s) by (apply (MovePieceGameover Hm)).
    unfold GameoverImplyNotSwapped; rewrite Ego, Esw; exact HG.
  }
  unfold CorrectWithoutGameover; split; [ exact L1 | split; assumption ].
Qed.

Lemma RotatePieceCorrectWithoutGameover : ∀ [cw s s']
  (Hc : CorrectWithoutGameover s)
  (Hm : RotatePiece cw s = Some s'),
  CorrectWithoutGameover s'.
Proof.
  intros.
  assert (HC2 : T2.CorrectWithoutGameover (s2 s)) by now destruct Hc; tauto.
  assert (HS : SwappedImplyHoldSome s) by now destruct Hc; tauto.
  assert (HG : GameoverImplyNotSwapped s) by now destruct Hc; tauto.
  set (LS := RotatePieceStep Hm).
  assert (E2 : T2.RotatePiece cw (s2 s) = Some (s2 s')) by now destruct LS; tauto.
  assert (Eh : hold s' = hold s) by now destruct LS; tauto.
  assert (Esw : swapped s' = swapped s) by now destruct LS; tauto.
  assert (L1 : T2.CorrectWithoutGameover (s2 s'))
    by (apply (@T2P.RotatePieceCorrectWithoutGameover cw (s2 s) (s2 s') HC2 E2)).
  assert (L2 : SwappedImplyHoldSome s')
    by (unfold SwappedImplyHoldSome; rewrite Eh, Esw; exact HS).
  assert (L3 : GameoverImplyNotSwapped s'). {
    assert (Ego : gameover s' = gameover s) by (apply (RotatePieceGameover Hm)).
    unfold GameoverImplyNotSwapped; rewrite Ego, Esw; exact HG.
  }
  unfold CorrectWithoutGameover; split; [ exact L1 | split; assumption ].
Qed.

Lemma FixPieceCorrectWithoutGameover : ∀ [pNew s s']
  (Hc : CorrectWithoutGameover s)
  (Hm : FixPiece pNew s = Some s'),
  CorrectWithoutGameover s'.
Proof.
  intros.
  assert (HC2 : T2.CorrectWithoutGameover (s2 s)) by now destruct Hc; tauto.
  set (LS := FixPieceStep Hm).
  assert (E2 : T2.FixPiece pNew (s2 s) = Some (s2 s')) by now destruct LS; tauto.
  assert (Esw : swapped s' = false) by now destruct LS; tauto.
  assert (L1 : T2.CorrectWithoutGameover (s2 s'))
    by (apply (@T2P.FixPieceCorrectWithoutGameover pNew (s2 s) (s2 s') HC2 E2)).
  assert (L2 : SwappedImplyHoldSome s')
    by (unfold SwappedImplyHoldSome; rewrite Esw; intros H1; discriminate H1).
  assert (L3 : GameoverImplyNotSwapped s')
    by (unfold GameoverImplyNotSwapped; intros _; exact Esw).
  unfold CorrectWithoutGameover; split; [ exact L1 | split; assumption ].
Qed.

(* HoldPiece is the one operation whose CorrectWithoutGameover-preservation
genuinely needs a gameover fact (via NewPieceStateCorrectWithoutGameover's
own weak-direction dependency) but HoldPieceStep already hands us
gameover s = false directly (part of its own guard), so the caller only ever
needs to supply the weak Gameover fact about s, not reconstruct anything. *)
Lemma HoldPieceCorrectWithoutGameover : ∀ [pNew s s']
  (Hc : CorrectWithoutGameover s)
  (Hg : ForbiddenGrid ∩ T1.mg (T2.s1 (s2 s)) ⊈ ∅ = true → T1.gameover (T2.s1 (s2 s)) = true)
  (Hm : HoldPiece pNew s = Some s'),
  CorrectWithoutGameover s'.
Proof.
  intros.
  assert (HC2 : T2.CorrectWithoutGameover (s2 s)) by now destruct Hc; tauto.
  set (LS := HoldPieceStep Hm).
  assert (Hgo : gameover s = false) by now destruct LS; tauto.
  assert (E2 : s2 s' = T2.UnchangedT2Part (s2 s) (T1.NewPieceState (HeldOrNew pNew s) (s1 (s2 s))))
    by now destruct LS; tauto.
  assert (Eh : hold s' = Some (p s)) by now destruct LS; tauto.
  assert (L1 : T2.CorrectWithoutGameover (s2 s'))
    by (rewrite E2; apply T2P.NewPieceStateCorrectWithoutGameover; (exact HC2 || exact Hg)).
  assert (L2 : SwappedImplyHoldSome s')
    by (unfold SwappedImplyHoldSome; rewrite Eh; intros _; discriminate).
  assert (L3 : GameoverImplyNotSwapped s'). {
    assert (Ego : gameover s' = gameover s)
      by (unfold gameover; rewrite E2; reflexivity).
    unfold GameoverImplyNotSwapped; rewrite Ego, Hgo.
    intros H1; discriminate H1.
  }
  unfold CorrectWithoutGameover; split; [ exact L1 | split; assumption ].
Qed.

Lemma NextCorrect : ∀ [e s s']
  (Hc : Correct s)
  (Hn : Next e s = Some s'),
  Correct s'.
Proof.
  intros e s s' Hc Hn.
  assert (HC2 : T2.Correct (s2 s)) by now destruct Hc; tauto.
  assert (HS : SwappedImplyHoldSome s) by now destruct Hc; tauto.
  assert (HG : GameoverImplyNotSwapped s) by now destruct Hc; tauto.
  (* Forwarded events: T2 preserves its own invariant; the T3 part is either
   * copied verbatim (Move, Rotate) or reset (Fix). *)
  assert (L1 : ∀ [dyx] (Hm : MovePiece dyx s = Some s'), Correct s'). {
    intros dyx Hm.
    set (LS := MovePieceStep Hm).
    assert (E2 : T2.MovePiece dyx (s2 s) = Some (s2 s')) by now destruct LS; tauto.
    assert (Eh : hold s' = hold s) by now destruct LS; tauto.
    assert (Esw : swapped s' = swapped s) by now destruct LS; tauto.
    assert (L1_1 : T2.Correct (s2 s'))
      by (apply (@T2P.NextCorrect (T2.Move dyx) (s2 s) (s2 s') HC2 E2)).
    assert (L1_2 : SwappedImplyHoldSome s')
      by (unfold SwappedImplyHoldSome; rewrite Eh, Esw; exact HS).
    assert (L1_3 : GameoverImplyNotSwapped s'). {
      assert (Ego : gameover s' = gameover s) by (apply (MovePieceGameover Hm)).
      unfold GameoverImplyNotSwapped; rewrite Ego, Esw; exact HG.
    }
    unfold Correct; split; [ exact L1_1 | split; assumption ].
  }
  assert (L2 : ∀ [cw] (Hm : RotatePiece cw s = Some s'), Correct s'). {
    intros cw Hm.
    set (LS := RotatePieceStep Hm).
    assert (E2 : T2.RotatePiece cw (s2 s) = Some (s2 s')) by now destruct LS; tauto.
    assert (Eh : hold s' = hold s) by now destruct LS; tauto.
    assert (Esw : swapped s' = swapped s) by now destruct LS; tauto.
    assert (L2_1 : T2.Correct (s2 s'))
      by (apply (@T2P.NextCorrect (T2.Rotate cw) (s2 s) (s2 s') HC2 E2)).
    assert (L2_2 : SwappedImplyHoldSome s')
      by (unfold SwappedImplyHoldSome; rewrite Eh, Esw; exact HS).
    assert (L2_3 : GameoverImplyNotSwapped s'). {
      assert (Ego : gameover s' = gameover s) by (apply (RotatePieceGameover Hm)).
      unfold GameoverImplyNotSwapped; rewrite Ego, Esw; exact HG.
    }
    unfold Correct; split; [ exact L2_1 | split; assumption ].
  }
  assert (L3 : ∀ [pNew] (Hm : FixPiece pNew s = Some s'), Correct s'). {
    intros pNew Hm.
    set (LS := FixPieceStep Hm).
    assert (E2 : T2.FixPiece pNew (s2 s) = Some (s2 s')) by now destruct LS; tauto.
    assert (Esw : swapped s' = false) by now destruct LS; tauto.
    assert (L3_1 : T2.Correct (s2 s'))
      by (apply (@T2P.NextCorrect (T2.Fix pNew) (s2 s) (s2 s') HC2 E2)).
    (* `swapped s' = false` makes both T3 invariants vacuous, whether or not the
     * fixation triggered a gameover. *)
    assert (L3_2 : SwappedImplyHoldSome s')
      by (unfold SwappedImplyHoldSome; rewrite Esw; intros H1; discriminate H1).
    assert (L3_3 : GameoverImplyNotSwapped s')
      by (unfold GameoverImplyNotSwapped; intros _; exact Esw).
    unfold Correct; split; [ exact L3_1 | split; assumption ].
  }
  assert (L4 : ∀ [pNew] (Hm : FallStep pNew s = Some s'), Correct s'). {
    intros pNew Hm.
    unfold FallStep in Hm.
    destruct MovePiece as [t |] eqn: Hd in Hm.
    - assert (L4_1 : MovePiece (-1, 0)%Z s = Some s') by (rewrite Hd; exact Hm).
      now apply L1 in L4_1.
    - Check (Hm : FixPiece pNew s = Some s').
      now apply L3 in Hm.
  }
  assert (L5 : ∀ (Hm : Next (Event2 T2.Stutter) s = Some s'), Correct s'). {
    intros Hm.
    assert (L5_1 : s' = s) by (apply (StutterStep Hm)).
    rewrite L5_1; unfold Correct; split; [ exact HC2 | split; assumption ].
  }
  assert (L6 : ∀ [pNew] (Hm : HoldPiece pNew s = Some s'), Correct s'). {
    intros pNew Hm.
    set (LS := HoldPieceStep Hm).
    assert (Hgo : gameover s = false) by now destruct LS; tauto.
    assert (E2 : s2 s' = T2.UnchangedT2Part (s2 s) (T1.NewPieceState (HeldOrNew pNew s) (s1 (s2 s))))
      by now destruct LS; tauto.
    assert (Eh : hold s' = Some (p s)) by now destruct LS; tauto.
    (* The T2 part only gets a new current piece, which T2 (hence T1) handles. *)
    assert (L6_1 : T2.Correct (s2 s'))
      by (rewrite E2; apply T2P.NewPieceStateCorrect; exact HC2).
    (* req-hold puts the current piece in the slot, so the slot is not empty. *)
    assert (L6_2 : SwappedImplyHoldSome s')
      by (unfold SwappedImplyHoldSome; rewrite Eh; intros _; discriminate).
    (* Holding requires ¬gameover and does not change it. *)
    assert (L6_3 : GameoverImplyNotSwapped s'). {
      assert (Ego : gameover s' = gameover s)
        by (unfold gameover; rewrite E2; reflexivity).
      unfold GameoverImplyNotSwapped; rewrite Ego, Hgo.
      intros H1; discriminate H1.
    }
    unfold Correct; split; [ exact L6_1 | split; assumption ].
  }
  destruct e as [e2 |].
  - destruct e2; eauto using L1, L2, L3, L4, L5.
  - eapp L6.
Qed.

Theorem SpecCorrect : ∀ e s s',
    (∀ p, Correct (Init p))
  ∧ (Correct s → Next e s = Some s' → Correct s').
Proof. split; eauto using InitCorrect, NextCorrect. Qed.


(* ========================================================================= *)
(* Step invariants                                                           *)
(* ========================================================================= *)

Theorem StepHoldMonotone (s s' : State) :
  HoldMonotone s s'.
Proof.
  unfold HoldMonotone.
  intros.
  enough (hold s' ≠ None) by trivial.
  destruct e; simpl in H2.
  - Check (H2 : NextT2Event e2 s = Some s').
    (* hold is unchanged by these events *)
    destruct e2 in H2; unfold NextT2Event in H2;
      (assert (L1 : hold s' = hold s) by now (
        apply MovePieceStep in H2 || apply RotatePieceStep in H2 ||
        apply FixPieceStep in H2 || apply FallStepStep in H2 ||
          (inject H2; congruence)));
      congruence.
  - Check (H2 : HoldPiece pNew s = Some s').
    assert (L1 : hold s' = Some (p s)) by now apply HoldPieceStep in H2.
    rewrite L1.
    discriminate.
Qed.

Theorem CorrectStepHold : ∀ [s] s'
  (Hc : Correct s),
  CorrectStep s s'.
Proof.
  intros.
  assert (L1 : T2.Correct (s2 s)) by now destruct Hc; tauto.
  split; (apply (T2P.CorrectStepHold _ L1) || apply StepHoldMonotone).
Qed.


(* ========================================================================= *)
(* Refinement                                                                *)
(* ========================================================================= *)

(***************)
(* T3RefinesT2 *)
(***************)

(* Proved before the step invariants, which reuse NextRefine to transport T2's
   own step invariants across the forwarded events. *)

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
Proof.
  intros s s' e2 Hn.
  unfold fₑ, fₛ, id.
  assert (L1 : ∀ [dyx] (Hm : MovePiece dyx s = Some s'),
               T2.Next (T2.Move dyx) (s2 s) = Some (s2 s'))
    by (intros dyx Hm; apply MovePieceStep in Hm as [H1 _]; exact H1).
  assert (L2 : ∀ [cw] (Hm : RotatePiece cw s = Some s'),
               T2.Next (T2.Rotate cw) (s2 s) = Some (s2 s'))
    by (intros cw Hm; apply RotatePieceStep in Hm as [H1 _]; exact H1).
  assert (L3 : ∀ [pNew] (Hm : FixPiece pNew s = Some s'),
               T2.Next (T2.Fix pNew) (s2 s) = Some (s2 s'))
    by (intros pNew Hm; apply FixPieceStep in Hm as [H1 _]; exact H1).
  assert (L4 : ∀ [pNew] (Hm : FallStep pNew s = Some s'),
               T2.Next (T2.Fall pNew) (s2 s) = Some (s2 s'))
    by (intros pNew Hm; apply FallStepStep in Hm as [H1 _]; exact H1).
  assert (L5 : ∀ (Hm : Next (Event2 T2.Stutter) s = Some s'),
               T2.Next T2.Stutter (s2 s) = Some (s2 s')). {
    intros Hm.
    assert (L5_1 : s' = s) by (apply (StutterStep Hm)).
    rewrite L5_1; reflexivity.
  }
  destruct e2; eauto using L1, L2, L3, L4, L5.
Qed.

Theorem SpecRefine : T3RefinesT2.
Proof. split; eauto using InitRefine, NextRefine. Qed.

(*****************)
(* T3AllowsAllT2 *)
(*****************)

(*
               es1
   T1.Init p   →         s1'
fₛ ↑           ⇓ map gₑ  ↑ fₛ
   T2.Init p   →         s2'
               es2
*)

(* Lemma feRetractsGe : ∀ e1, fₑ (gₑ e1) = e1.
Proof. destruct e1; now simpl. Qed. *)

Lemma StepLifts :
  ∀ [e2 s2 s2' s3]
    (H1 : fₛ s3 = s2)
    (H2 : T2.Next e2 s2 = Some s2'),
    ∃ s3', T3.NextT2Event e2 s3 = Some s3' ∧ fₛ s3' = s2'.
Proof.
  intros.
  destruct (T3.NextT2Event e2 s3) eqn: Hn.
  - Check (Hn : NextT2Event e2 s3 = Some s).
    assert (L1 : fₛ s = s2'). {
      assert (L1_1 : T2.Next e2 (fₛ s3) = Some (fₛ s))
        by now apply NextRefine in Hn.
      assert (L1_2 : T2.Next e2 s2 = Some (fₛ s))
        by now rewrite H1 in L1_1.
      now rewrite H2 in L1_2; inject L1_2.
    }
    enough (Some s = Some s ∧ fₛ s = s2') by now exists s.
    split; (reflexivity || exact L1).
  - Check (Hn : NextT2Event e2 s3 = None).
    unfold T2.Next in H2.
    unfold NextT2Event, MovePiece, RotatePiece, FixPiece in Hn.
    unfold fₛ in H1.
    rewrite <- H1 in H2.
    assert (L1 : ∀ pNew
        (Hf1 : T2.FallStep pNew (T3.s2 s3) = Some s2')
        (Hf2 : FallStep pNew s3 = None),
        ∃ s3' : State, None = Some s3' ∧ fₛ s3' = s2'). {
      intros.
      keep_only Hf1 Hf2.
      unfold T2.FallStep in Hf1.
      unfold FallStep, MovePiece in Hf2.
      destruct (T2.MovePiece ((-1)%Z, 0%Z) (T3.s2 s3)).
      -- unfold FallStep in Hf2. discriminate Hf2.
      -- simpl in Hf2.
         unfold FixPiece in Hf2.
         rewrite Hf1 in Hf2.
         discriminate Hf2.
    }
    destruct e2; simpl in Hn;
      (try rewrite H2 in Hn; discriminate Hn) || eapp L1.
Qed.

Theorem T3AllowsAllT2Hold : T3AllowsAllT2.
Proof.
  (* generalize the starting states so the IH applies at every point along the run *)
  assert (L1 : ∀ es2 s2 s3 s2'
      (Hfs : fₛ s3 = s2)
      (Hrun : RunT2 es2 s2 = Some s2'),
      ∃ s3', RunT3 es2 s3 = Some s3' /\ fₛ s3' = s2'). {
    intros es2.
    induction es2 as [| e2 es2' IH]. intros.
    - (* es2 = [] : RunT2 returns s2 itself *)
      exists s3. simpl in Hrun. split; (reflexivity || congruence).
    - (* es2 = e2 :: es2' *)
      intros.
      simpl in Hrun.
      destruct (T2.Next e2 s2) as [s2'' | ] eqn:Hstep; [ | discriminate].
      (* apply the single-step lemma to lift this step to T3 *)
      destruct (StepLifts Hfs Hstep) as [s3'' [Hstep3 Hfs2]].
      simpl. rewrite Hstep3.
      (* recurse on the rest of the trace, from (s1'', s2'') *)
      eapp IH.
  }
  unfold T3AllowsAllT2. intros p es2 s2'.
  enough (fₛ (T3.Init p) = T2.Init p)
    by now apply (L1 es2 (T2.Init p) (T3.Init p) s2').
  assert (L2 : ∀ p, fₛ (T3.Init p) = T2.Init p)
    by now pose proof SpecRefine; tauto.
  exact (L2 p).
Qed.
