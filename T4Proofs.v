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

(* req-preview-pop: drawing preserves the Draw invariant.
 * There are two cases:
 * - the bag had a single piece left: it is refilled to MaxBagLen, so no preview
 *   entry comes from it yet and BagNextConsistentD is vacuous (k = 0);
 * - the bag had at least two: one piece is popped from its end onto the end of
 *   the preview, and every other preview entry shifts down by one. *)
Lemma DrawNextPieceCorrect : ∀ (dd : Draw) (bagNew : ℕ → Piece)
  (HB : PieceSet bagNew)
  (HD : CorrectD dd),
  CorrectD (snd (DrawNextPiece dd bagNew)).
Proof.
  intros.
  assert (HP : PieceSet (bag_ dd)) by now destruct HD; tauto.
  assert (HL : 0 < bagLen_ dd) by now destruct HD; tauto.
  assert (HC : BagNextConsistentD dd) by now destruct HD; tauto.
  assert (HM : MaxBagLen > 0) by exact AxiomsMaxBagLen.
  (* The three fields of the drawn Draw, by computation. *)
  assert (Ebag : bag_ (snd (DrawNextPiece dd bagNew))
               = if bagLen_ dd <=? 1 then bagNew else bag_ dd) by reflexivity.
  assert (Elen : bagLen_ (snd (DrawNextPiece dd bagNew))
               = if bagLen_ dd <=? 1 then MaxBagLen else bagLen_ dd - 1) by reflexivity.
  assert (Enext : next_ (snd (DrawNextPiece dd bagNew))
                = ShiftNext (next_ dd) (bag_ dd (bagLen_ dd - 1))) by reflexivity.
  unfold BagNextConsistentD in HC; cbv zeta in HC.
  destruct (bagLen_ dd <=? 1) eqn: Hs.
  - (* refill: the bag is empty (or nearly), so it is refilled to MaxBagLen and
    no preview entry has been drawn from it yet. BagNextConsistentD is
    vacuous (k = 0). *)
    assert (L1 : PieceSet (bag_ (snd (DrawNextPiece dd bagNew))))
      by now rewrite Ebag; exact HB.
    assert (L2 : 0 < bagLen_ (snd (DrawNextPiece dd bagNew)))
      by now rewrite Elen; exact HM.
    assert (L3 : BagNextConsistentD (snd (DrawNextPiece dd bagNew))). {
      unfold BagNextConsistentD; cbv zeta; rewrite Elen.
      intros i Hi; exfalso; keep_only Hi; lia.
    }
    unfold CorrectD; split; [ | split ]; auto using L1, L2, L3.
  - (* at least two pieces in the bag: one is popped onto the end of the
     * preview, and every other preview entry shifts down by one. *)
    assert (Htwo : 2 <= bagLen_ dd) by (apply Nat.leb_gt in Hs; lia).
    assert (L1 : PieceSet (bag_ (snd (DrawNextPiece dd bagNew))))
      by now rewrite Ebag; exact HP.
    assert (L2 : 0 < bagLen_ (snd (DrawNextPiece dd bagNew)))
      by now rewrite Elen; keep_only Htwo; lia.
    assert (L3 : BagNextConsistentD (snd (DrawNextPiece dd bagNew))). {
      unfold BagNextConsistentD; cbv zeta.
      rewrite Ebag, Elen, Enext.
      intros i Hi.
      enough ((if NextLen - i - 1 =? NextLen - 1
        then bag_ dd (bagLen_ dd - 1)
        else next_ dd (NextLen - i - 1 + 1)) = bag_ dd (bagLen_ dd - 1 + i))
        by now unfold ShiftNext; cbv beta.
      destruct i as [| i'].
      * (* i = 0: the piece popped from the bag lands at the end of the preview *)
        assert (E : (NextLen - 0 - 1 =? NextLen - 1) = true)
          by (apply Nat.eqb_eq; lia).
        rewrite E; f_equal; keep_only Htwo; lia.
      * (* i = S i': every other preview entry is the previous one, shifted down by one *)
        assert (E : (NextLen - S i' - 1 =? NextLen - 1) = false)
          by now apply Nat.eqb_neq; keep_only Hi; lia.
        enough (next_ dd (NextLen - S i' - 1 + 1) = bag_ dd (bagLen_ dd - 1 + S i'))
          by now rewrite E.
        assert (Hk : i' < min (MaxBagLen - bagLen_ dd) NextLen)
          by (keep_only Hi Htwo; lia).
        assert (L3_1 : next_ dd (NextLen - i' - 1) = bag_ dd (bagLen_ dd + i'))
          by exact (HC i' Hk).
        assert (L3_2 : next_ dd (NextLen - S i') = bag_ dd (bagLen_ dd + i')). {
          now replace (NextLen - i' - 1) with (NextLen - S i') in L3_1
            by (keep_only Hi; lia).
        }
        enough (next_ dd (NextLen - S i') = bag_ dd (bagLen_ dd - 1 + S i')). {
          now replace (NextLen - S i' - 1 + 1) with (NextLen - S i')
            by (keep_only Hi; lia).
        }
        rewrite L3_2; f_equal; keep_only Htwo; lia.
    }
    unfold CorrectD; split; [ | split ]; auto using L1, L2, L3.
Qed.

Lemma DrawAfterCorrect : ∀ (s : State) (bagNew : ℕ → Piece)
  (HB : PieceSet bagNew)
  (Hc : Correct s),
  CorrectD (DrawAfter s bagNew).
Proof.
  intros.
  unfold DrawAfter; apply DrawNextPieceCorrect; (exact HB || now destruct Hc).
Qed.

Lemma HoldDrawCorrect : ∀ (s : State) (bagNew : ℕ → Piece)
  (HB : PieceSet bagNew)
  (Hc : Correct s),
  CorrectD (HoldDraw s bagNew).
Proof.
  intros.
  unfold HoldDraw; destruct (hold s).
  - now destruct Hc.
  - now apply DrawAfterCorrect.
Qed.

Lemma DrawAfterCorrectWithoutGameover : ∀ (s : State) (bagNew : ℕ → Piece)
  (HB : PieceSet bagNew)
  (Hc : CorrectWithoutGameover s),
  CorrectD (DrawAfter s bagNew).
Proof.
  intros.
  unfold DrawAfter; apply DrawNextPieceCorrect; (exact HB || now destruct Hc).
Qed.

Lemma HoldDrawCorrectWithoutGameover : ∀ (s : State) (bagNew : ℕ → Piece)
  (HB : PieceSet bagNew)
  (Hc : CorrectWithoutGameover s),
  CorrectD (HoldDraw s bagNew).
Proof.
  intros.
  unfold HoldDraw; destruct (hold s).
  - now destruct Hc.
  - now apply DrawAfterCorrectWithoutGameover.
Qed.

(* One step of the preview-filling loop. *)
Lemma BuildInitNextS : ∀ (dd : Draw) (i : ℕ) (bags : ℕ → ℕ → Piece) (bagIdx : ℕ),
  BuildInitNext dd (S i) bags bagIdx
  = BuildInitNext (snd (DrawNextPiece dd (bags bagIdx))) i bags
      (bagIdx + (if bagLen_ dd =? 1 then 1 else 0)).
Proof. reflexivity. Qed.

Lemma BuildInitNextCorrect : ∀ (i : ℕ) (bags : ℕ → ℕ → Piece) (bagIdx : ℕ) (dd : Draw)
  (HB : ∀ j, PieceSet (bags j))
  (HD : CorrectD dd),
  CorrectD (fst (BuildInitNext dd i bags bagIdx)).
Proof.
  induction i as [| i' IH]; intros bags bagIdx dd HB HD.
  - (* i = 0 *) exact HD.
  - (* i = S i' *)
    rewrite BuildInitNextS.
    apply IH; [ exact HB | ].
    apply DrawNextPieceCorrect; (apply HB || exact HD).
Qed.

(* req-preview-init *)
Lemma InitDrawCorrect : ∀ (bags : ℕ → ℕ → Piece) (HB : ∀ i, PieceSet (bags i)),
  CorrectD (snd (InitPieceAndDraw bags HB)).
Proof.
  intros.
  assert (HM : MaxBagLen > 0) by now exact AxiomsMaxBagLen.
  (* The seed Draw has a full bag; its `next_` is arbitrary, which is harmless
   * because a full bag makes BagNextConsistentD vacuous (k = 0). *)
  set (B := {| bag_ := bags 0; bagLen_ := MaxBagLen; next_ := bags 0 |}).
  assert (L1 : PieceSet (bag_ B)) by now apply HB.
  assert (L2 : 0 < bagLen_ B) by now exact HM.
  assert (L3 : BagNextConsistentD B). {
    unfold BagNextConsistentD; cbv zeta; simpl.
    intros i Hi; exfalso; keep_only Hi; lia.
  }
  assert (HD0 : CorrectD B). {
    unfold CorrectD; split; [ | split ]; auto using L1, L2, L3.
  }
  unfold InitPieceAndDraw; cbv zeta.
  (*** *)
  destruct (BuildInitNext {| bag_ := bags 0; bagLen_ := MaxBagLen; next_ := bags 0 |}
              NextLen bags 1) as [d1 bagIdx] eqn: Hb.
  assert (Hd1 : d1 = fst (BuildInitNext
                            {| bag_ := bags 0; bagLen_ := MaxBagLen; next_ := bags 0 |}
                            NextLen bags 1))
    by (rewrite Hb; reflexivity).
  assert (HD1 : CorrectD d1)
    by (rewrite Hd1; apply BuildInitNextCorrect; assumption).
  apply DrawNextPieceCorrect; (apply HB || exact HD1).
Qed.


(* ========================================================================= *)
(* Helpers: what each event does to the two components of the state          *)
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

Lemma MovePieceStep : ∀ [s s' dyx]
  (Hn : MovePiece dyx s = Some s'),
  T3.MovePiece dyx (s3 s) = Some (s3 s') ∧ d s' = d s.
Proof.
  intros.
  unfold MovePiece, option_map in Hn.
  destruct (T3.MovePiece dyx (s3 s)) as [t |] eqn: Hd.
  - (* Some t *)
    enough (Some t = Some (s3 s') ∧ d s' = d s) by trivial.
    assert (L1 : s' = UnchangedT4Part s t) by (inject Hn; now symmetry).
    rewrite L1; split; reflexivity.
  - (* None *)
    enough (None = Some (s3 s') ∧ d s' = d s) by trivial.
    discriminate Hn.
Qed.

Lemma RotatePieceStep : ∀ [s s' cw]
  (Hn : RotatePiece cw s = Some s'),
  T3.RotatePiece cw (s3 s) = Some (s3 s') ∧ d s' = d s.
Proof.
  intros.
  unfold RotatePiece, option_map in Hn.
  destruct (T3.RotatePiece cw (s3 s)) as [t |] eqn: Hd.
  - (* Some t *)
    enough (Some t = Some (s3 s') ∧ d s' = d s) by trivial.
    assert (L1 : s' = UnchangedT4Part s t) by (inject Hn; now symmetry).
    rewrite L1; split; reflexivity.
  - (* None *)
    enough (None = Some (s3 s') ∧ d s' = d s) by trivial.
    discriminate Hn.
Qed.

(* A successful MovePiece proves T3's own guard held. *)
Lemma MovePieceNotGameover : ∀ [s s' dyx]
  (H1 : MovePiece dyx s = Some s'),
  gameover s = false.
Proof.
  intros.
  destruct (MovePieceStep H1) as [H2 _].
  exact (T3P.MovePieceNotGameover H2).
Qed.

(* A successful RotatePiece proves T3's own guard held. *)
Lemma RotatePieceNotGameover : ∀ [s s' cw]
  (H1 : RotatePiece cw s = Some s'),
  gameover s = false.
Proof.
  intros.
  destruct (RotatePieceStep H1) as [H2 _].
  exact (T3P.RotatePieceNotGameover H2).
Qed.

Lemma MovePieceMgGameoverUnchanged : ∀ [s s' dyx]
  (Hn : MovePiece dyx s = Some s'),
  mg s' = mg s ∧ gameover s' = gameover s.
Proof.
  intros.
  destruct (MovePieceStep Hn) as [H1 _].
  split.
  - exact (T3P.MovePieceMgUnchanged H1).
  - exact (T3P.MovePieceGameover H1).
Qed.

Lemma RotatePieceMgGameoverUnchanged : ∀ [s s' cw]
  (Hn : RotatePiece cw s = Some s'),
  mg s' = mg s ∧ gameover s' = gameover s.
Proof.
  intros.
  destruct (RotatePieceStep Hn) as [H1 _].
  split.
  - exact (T3P.RotatePieceMgUnchanged H1).
  - exact (T3P.RotatePieceGameover H1).
Qed.

Lemma MovePieceFail : ∀ [s dyx]
  (Hn : MovePiece dyx s = None),
  T3.MovePiece dyx (s3 s) = None.
Proof.
  intros.
  unfold MovePiece, option_map in Hn.
  destruct (T3.MovePiece dyx (s3 s)) as [t |] eqn: Hd.
  - (* Some t *)
    enough (Some t = None) by trivial.
    discriminate Hn.
  - (* None *)
    reflexivity.
Qed.

Lemma FixPieceStep : ∀ [s s' bagNew] [H : PieceSet bagNew]
  (Hn : FixPiece bagNew H s = Some s'),
    T3.FixPiece (next s 0) (s3 s) = Some (s3 s')
  ∧ d s' = DrawAfter s bagNew.
Proof.
  intros.
  rewrite FixPieceEq in Hn; unfold option_map in Hn.
  destruct (T3.FixPiece (next s 0) (s3 s)) as [t |] eqn: Hf.
  - (* Some t *)
    enough (Some t = Some (s3 s') ∧ d s' = DrawAfter s bagNew) by trivial.
    assert (L1 : s' = mkState t (DrawAfter s bagNew)) by (inject Hn; now symmetry).
    rewrite L1; split; reflexivity.
  - (* None *)
    enough (None = Some (s3 s') ∧ d s' = DrawAfter s bagNew) by trivial.
    discriminate Hn.
Qed.

Lemma HoldPieceStep : ∀ [s s' bagNew] [H : PieceSet bagNew]
  (Hn : HoldPiece bagNew H s = Some s'),
    gameover s = false
  ∧ T3.HoldPiece (next s 0) (s3 s) = Some (s3 s')
  ∧ d s' = HoldDraw s bagNew.
Proof.
  intros.
  rewrite HoldPieceEq in Hn.
  destruct (gameover s) eqn: Hg; [ discriminate Hn | ].
  unfold option_map in Hn.
  destruct (T3.HoldPiece (next s 0) (s3 s)) as [t |] eqn: Hh.
  - (* Some t *)
    enough (false = false ∧ Some t = Some (s3 s') ∧ d s' = HoldDraw s bagNew) by trivial.
    assert (L1 : s' = mkState t (HoldDraw s bagNew)) by (inject Hn; now symmetry).
    rewrite L1; repeat split; reflexivity.
  - (* None *)
    enough (false = false ∧ None = Some (s3 s') ∧ d s' = HoldDraw s bagNew) by trivial.
    discriminate Hn.
Qed.

Lemma HoldPieceMgGameoverUnchanged : ∀ [bagNew] [H : PieceSet bagNew] [s s']
  (Hn : HoldPiece bagNew H s = Some s'),
  mg s' = mg s ∧ gameover s' = gameover s.
Proof.
  intros.
  destruct (HoldPieceStep Hn) as (_ & E3 & _).
  exact (T3P.HoldPieceMgGameoverUnchanged E3).
Qed.

Lemma FallStepStep : ∀ [s s' bagNew] [H : PieceSet bagNew]
  (Hn : FallStep bagNew H s = Some s'),
    T3.FallStep (next s 0) (s3 s) = Some (s3 s')
  ∧ (d s' = d s ∨ d s' = DrawAfter s bagNew).
Proof.
  intros.
  unfold FallStep in Hn.
  destruct MovePiece as [t |] eqn: Hm in Hn.
  - (* Some t: the piece moved down: the preview is untouched *)
    enough (T3.FallStep (next s 0) (s3 s) = Some (s3 s')
      ∧ (d s' = d s ∨ d s' = DrawAfter s bagNew)) by trivial.
    assert (L1 : MovePiece (-1, 0)%Z s = Some s') by (rewrite Hm; exact Hn).
    assert (LS := MovePieceStep L1); destruct LS as [E3 Ed].
    unfold T3.FallStep; rewrite E3.
    split; [ reflexivity | left; exact Ed ].
  - (* None: the piece fixed: a new piece is popped from the preview *)
    enough (T3.FallStep (next s 0) (s3 s) = Some (s3 s')
      ∧ (d s' = d s ∨ d s' = DrawAfter s bagNew)) by trivial.
    assert (L1 : T3.MovePiece (-1, 0)%Z (s3 s) = None) by (apply MovePieceFail; exact Hm).
    assert (LS := FixPieceStep Hn); destruct LS as [E3 Ed].
    unfold T3.FallStep; rewrite L1, E3.
    split; [ reflexivity | right; exact Ed ].
Qed.

Lemma StutterStep : ∀ [s s']
  (Hn : Next Stutter s = Some s'),
  s = s'.
Proof. intros; now unfold Next in Hn; inject Hn. Qed.


(* ========================================================================= *)
(* State invariants                                                          *)
(* ========================================================================= *)

Lemma InitCorrect : ∀ (bags : ℕ → ℕ → Piece) (HB : ∀ i, PieceSet (bags i)),
  Correct (Init bags HB).
Proof.
  intros.
  assert (Es3 : s3 (Init bags HB) = T3.Init (InitPiece bags HB)). {
    unfold Init, InitPiece.
    destruct (InitPieceAndDraw bags HB) as [p0 dd]; reflexivity.
  }
  assert (Ed : d (Init bags HB) = snd (InitPieceAndDraw bags HB)). {
    unfold Init.
    destruct (InitPieceAndDraw bags HB) as [p0 dd]; reflexivity.
  }
  assert (L1 : T3.Correct (s3 (Init bags HB)))
    by now rewrite Es3; apply T3P.InitCorrect.
  assert (L2 : CorrectD (d (Init bags HB)))
    by now rewrite Ed; apply InitDrawCorrect.
  unfold Correct; split; auto using L1, L2.
  Qed.

Lemma MovePieceCorrectWithoutGameover : ∀ [dyx s s']
  (Hc : CorrectWithoutGameover s)
  (Hm : MovePiece dyx s = Some s'),
  CorrectWithoutGameover s'.
Proof.
  intros.
  assert (HC3 : T3.CorrectWithoutGameover (s3 s)) by now destruct Hc.
  assert (HCD : CorrectD (d s)) by now destruct Hc.
  set (LS := MovePieceStep Hm).
  assert (E3 : T3.MovePiece dyx (s3 s) = Some (s3 s')) by now destruct LS; tauto.
  assert (Ed : d s' = d s) by now destruct LS; tauto.
  unfold CorrectWithoutGameover; split.
  - apply (@T3P.MovePieceCorrectWithoutGameover dyx (s3 s) (s3 s') HC3 E3).
  - rewrite Ed; exact HCD.
Qed.

Lemma RotatePieceCorrectWithoutGameover : ∀ [cw s s']
  (Hc : CorrectWithoutGameover s)
  (Hm : RotatePiece cw s = Some s'),
  CorrectWithoutGameover s'.
Proof.
  intros.
  assert (HC3 : T3.CorrectWithoutGameover (s3 s)) by now destruct Hc.
  assert (HCD : CorrectD (d s)) by now destruct Hc.
  set (LS := RotatePieceStep Hm).
  assert (E3 : T3.RotatePiece cw (s3 s) = Some (s3 s')) by now destruct LS; tauto.
  assert (Ed : d s' = d s) by now destruct LS; tauto.
  unfold CorrectWithoutGameover; split.
  - apply (@T3P.RotatePieceCorrectWithoutGameover cw (s3 s) (s3 s') HC3 E3).
  - rewrite Ed; exact HCD.
Qed.

Lemma FixPieceCorrectWithoutGameover : ∀ [bagNew] [H : PieceSet bagNew] [s s']
  (Hc : CorrectWithoutGameover s)
  (Hm : FixPiece bagNew H s = Some s'),
  CorrectWithoutGameover s'.
Proof.
  intros.
  assert (HC3 : T3.CorrectWithoutGameover (s3 s)) by now destruct Hc.
  set (LS := FixPieceStep Hm).
  assert (E3 : T3.FixPiece (next s 0) (s3 s) = Some (s3 s')) by now destruct LS; tauto.
  assert (Ed : d s' = DrawAfter s bagNew) by now destruct LS; tauto.
  unfold CorrectWithoutGameover; split.
  - apply (@T3P.FixPieceCorrectWithoutGameover (next s 0) (s3 s) (s3 s') HC3 E3).
  - rewrite Ed; apply DrawAfterCorrectWithoutGameover; assumption.
Qed.

(* Hold's own weak-gameover need is unchanged in shape from T3's; it just gets
threaded one level deeper through the s3 projection. *)
Lemma HoldPieceCorrectWithoutGameover : ∀ [bagNew] [H : PieceSet bagNew] [s s']
  (Hc : CorrectWithoutGameover s)
  (Hg : ForbiddenGrid ∩ T1.mg (T2.s1 (T3.s2 (s3 s))) ⊈ ∅ = true
        → T1.gameover (T2.s1 (T3.s2 (s3 s))) = true)
  (Hm : HoldPiece bagNew H s = Some s'),
  CorrectWithoutGameover s'.
Proof.
  intros.
  assert (HC3 : T3.CorrectWithoutGameover (s3 s)) by now destruct Hc.
  set (LS := HoldPieceStep Hm).
  assert (E3 : T3.HoldPiece (next s 0) (s3 s) = Some (s3 s')) by now destruct LS; tauto.
  assert (Ed : d s' = HoldDraw s bagNew) by now destruct LS; tauto.
  unfold CorrectWithoutGameover; split.
  - apply (@T3P.HoldPieceCorrectWithoutGameover (next s 0) (s3 s) (s3 s') HC3 Hg E3).
  - rewrite Ed; apply HoldDrawCorrectWithoutGameover; assumption.
Qed.

Lemma NextCorrect : ∀ [e s s']
  (Hc : Correct s)
  (Hn : Next e s = Some s'),
  Correct s'.
Proof.
  intros.
  assert (HC3 : T3.Correct (s3 s)) by now destruct Hc.
  assert (HCD : CorrectD (d s)) by now destruct Hc.
  (* Move and Rotate are forwarded and leave the Draw untouched. *)
  assert (L1 : ∀ [dyx] (Hm : MovePiece dyx s = Some s'), Correct s'). {
    intros.
    set (LS := MovePieceStep Hm).
    assert (E3 : T3.MovePiece dyx (s3 s) = Some (s3 s')) by now destruct LS; tauto.
    assert (Ed : d s' = d s) by now destruct LS; tauto.
    unfold Correct; split.
    - apply (@T3P.NextCorrect (T3.Event2 (T2.Move dyx)) (s3 s) (s3 s') HC3 E3).
    - rewrite Ed; exact HCD.
  }
  assert (L2 : ∀ [cw] (Hm : RotatePiece cw s = Some s'), Correct s'). {
    intros.
    set (LS := RotatePieceStep Hm).
    assert (E3 : T3.RotatePiece cw (s3 s) = Some (s3 s')) by now destruct LS; tauto.
    assert (Ed : d s' = d s) by now destruct LS; tauto.
    unfold Correct; split.
    - apply (@T3P.NextCorrect (T3.Event2 (T2.Rotate cw)) (s3 s) (s3 s') HC3 E3).
    - rewrite Ed; exact HCD.
  }
  (* Fix pops the preview; the popped piece is the one T3 receives. *)
  assert (L3 : ∀ [bagNew] [H : PieceSet bagNew]
               (Hm : FixPiece bagNew H s = Some s'), Correct s'). {
    intros.
    set (LS := FixPieceStep Hm).
    assert (E3 : T3.FixPiece (next s 0) (s3 s) = Some (s3 s')) by now destruct LS; tauto.
    assert (Ed : d s' = DrawAfter s bagNew) by now destruct LS; tauto.
    unfold Correct; split.
    - apply (@T3P.NextCorrect (T3.Event2 (T2.Fix (next s 0))) (s3 s) (s3 s') HC3 E3).
    - rewrite Ed; apply DrawAfterCorrect; assumption.
  }
  assert (L4 : ∀ [bagNew] [H : PieceSet bagNew]
               (Hm : FallStep bagNew H s = Some s'), Correct s'). {
    intros.
    unfold FallStep in Hm.
    destruct MovePiece as [t |] eqn: Hd in Hm.
    - (* Some t *)
      Check (Hd : MovePiece ((-1)%Z, 0%Z) s = Some t).
      assert (L4_1 : MovePiece (-1, 0)%Z s = Some s') by (rewrite Hd; exact Hm).
      now apply L1 in L4_1.
    - (* None *)
      Check (Hm : FixPiece bagNew H s = Some s').
      now apply L3 in Hm.
  }
  (* Hold consumes the preview only when the hold slot is empty. *)
  assert (L5 : ∀ [bagNew] [H : PieceSet bagNew]
               (Hm : HoldPiece bagNew H s = Some s'), Correct s'). {
    intros.
    set (LS := HoldPieceStep Hm).
    assert (E3 : T3.HoldPiece (next s 0) (s3 s) = Some (s3 s')) by now destruct LS; tauto.
    assert (Ed : d s' = HoldDraw s bagNew) by now destruct LS; tauto.
    unfold Correct; split.
    - apply (@T3P.NextCorrect (T3.Hold (next s 0)) (s3 s) (s3 s') HC3 E3).
    - rewrite Ed; apply HoldDrawCorrect; assumption.
  }
  assert (L6 : ∀ (Hm : Next Stutter s = Some s'), Correct s'). {
    intros; keep_only Hm Hc.
    rewrite <- (StutterStep Hm); exact Hc.
  }
  destruct e eqn: He; (eapp L1 || eapp L2 || eapp (L3 bagNew H) ||
    eapp L4 || eapp (L5 bagNew H) || eapp L6).
Qed.

Theorem SpecCorrect : ∀ e s s',
    (∀ bags HB, Correct (Init bags HB))
  ∧ (Correct s → Next e s = Some s' → Correct s').
Proof. split; eauto using InitCorrect, NextCorrect. Qed.


(* ========================================================================= *)
(* Step invariants                                                           *)
(* ========================================================================= *)

Theorem CorrectStepHold : ∀ [s] s'
  (Hc : Correct s),
  CorrectStep s s'.
Proof.
  intros.
  assert (L1 : T3.Correct (s3 s)) by now destruct Hc; tauto.
  split; apply (T3P.CorrectStepHold _ L1).
Qed.


(* ========================================================================= *)
(* Refinement                                                                *)
(* ========================================================================= *)

(* Proved before the step invariants, which reuse NextRefine to transport T3's
   step invariants across every T4 event. *)

Lemma InitRefine : ∀ bags HSet,
  fₛ (T4.Init bags HSet) = T3.Init (T4.InitPiece bags HSet).
Proof.
  intros; unfold fₛ, Init, InitPiece.
  destruct (InitPieceAndDraw bags HSet); reflexivity.
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
Proof.
  intros.
  destruct e4; now (apply MovePieceStep in H1 || apply RotatePieceStep in H1 ||
    eapply FixPieceStep in H1 || apply FallStepStep in H1 ||
    apply HoldPieceStep in H1 ||
    (apply StutterStep in H1; unfold fₛ; now rewrite H1)); simpl.
Qed.

Theorem T4RefinesT3Hold : T4RefinesT3.
Proof. split; auto using InitRefine, NextRefine. Qed.


(* ========================================================================= *)
(* Helpers for refining models                                               *)
(* ========================================================================= *)

Lemma MovePieceUnchangedGameover : ∀ [s s' dyx]
  (H1 : MovePiece dyx s = Some s'),
  gameover s' = gameover s.
Proof.
  intros.
  assert (L1 : T3.MovePiece dyx (s3 s) = Some (s3 s'))
    by (apply MovePieceStep in H1; tauto).
  unfold gameover; exact (T3P.MovePieceGameover L1).
Qed.

Lemma RotatePieceUnchangedGameover : ∀ [s s' cw]
  (H1 : RotatePiece cw s = Some s'),
  gameover s' = gameover s.
Proof.
  intros.
  assert (L1 : T3.RotatePiece cw (s3 s) = Some (s3 s'))
    by (apply RotatePieceStep in H1; tauto).
  unfold gameover; exact (T3P.RotatePieceGameover L1).
Qed.
