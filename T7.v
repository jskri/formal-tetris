(***************************************************************************
This model extends T6 with the multi-player mechanics.


# New addressed requirements

req-multi, req-multi-succ, req-multi-target-nonself, req-multi-garbage-gen,
req-multi-garbage-cancel, req-multi-garbage-send,
req-multi-garbage-materialize, req-multi-gameover, req-multi-winner

(see definitions_requirements.md)


# Design

T7 generalizes T6 for the multi-player game. It also describes the
single-player game in the special case where the player count is one. In this
case, it is equivalent to T6.

## New stop conditions

The main mechanics added to the multi-player game is the garbage. When a player
clears enough lines, it sends one-hole lines to another player (the target).
Garbage (i.e. one-hole lines) appears at the bottom of the target's main grid
and pushes existing blocks upward. This causes a new gameover condition that
occurs when some occupied blocks are pushed above the main grid's top. There is
also a new condition for the game to stop, which happens when only one player
remains alive (i.e. not gameover and not disconnected, see below). This player
is called the winner. We do not call this new condition a gameover to keep the
same gameover meaning as in the previous models.

Note that all the garbage mechanics occur when a piece fixes.

## Network

The network is also modeled. Players communicate with messages to send garbage,
and declare gameover.

The network has a star topology. One player, the host, relays all messages
between other players. When the host detects its connection to one player is
down, it sends a dedicated message to other players to notify them. When the
host itself goes offline, all players are disconnected.

The network is reliable: no message loss, no duplication, no reordering.
However, messages can take an arbitrary amount of time to travel. This means
for instance that a player A can be disconnected or gameover, and another
player B can believe it is still playing. Each player has its own view of the
connectedness and "liveness" of other players. Also when the host is down, the
non-host players can take some time to notice they are disconnected (see
`NoticeDisconnection`).

However, messages do not lie. For instance when a player receives a message
declaring player A is gameover, player A really is (because gameover is
monotone: once reached, it cannot be undone).

## State

The state of this model is different in nature from previous ones. While
previous models described a single "process", this one describes a whole
network. A state in this model has one T6 state per player, which is extended
with the received garbage, the target and the gameover/connected views (see
`s6`, `garbage`, `target`, `gameoverView` and `connectedView`). These belong to
the same player/process. However, the remaining fields describe the network;
they are not a local view of any player: they describe which player is
connected, and which messages are in flight (see `connected` and `messages`).

## Events

All T6 events' guards are updated to hold only if the player is not the winner.
`FixPiece` is the only event heavily modified to describe the garbage mechanics
(sending garbage and materializing some).

New events relate to the network: receiving a message (`ReceiveMessage`),
disconnecting from the network (`DisconnectPlayer`) and noticing oneself is
disconnected (`NoticeDisconnection`).


# Parameters

The Player type is opaque: it is only comparable for boolean equality and ordered
(each player has a successor, forming a cyclic permutation). The player count is
also a parameter of the model. The fact that it is non-null follows from the
cyclic permutation structure and the existence of the host.


# Refinement

This model introduces one state per player, therefore there is not one
refinement mapping, but one per player. However, the garbage materialization
mechanism is genuinely new, so the mapping must exclude it, since it has no
counterpart in T6. Another change in T7 is that the game now stops for the
winner, although it is not gameover. But this is not a problem, since refinement
only considers valid steps.

***************************************************************************)

From Tetris Require T4 T5 T6.
Import T1(Piece, Grid, L, HW, YX, H, W, Y, X, Full, Empty, InitialMainGrid, ForbiddenGrid).
Import (notations) T1.
From Tetris Require Import Notations.
From Stdlib Require Import List.
Import ListNotations.

#[local] Coercion Z.of_nat : ℕ >-> ℤ. (* safe embedding *)
#[local] Arguments pair {A B} & a b. (* to coerce pair components *)
Declare Scope player_scope.
Delimit Scope player_scope with player.
#[local] Open Scope nat_scope.

Parameter Player : Type.
Parameter Host : Player. (* one player is the host (the single player if PlayerCount = 1) *)
Parameter PlayerEqb : Player → Player → bool.
Parameter PlayerNext : Player → Player. (* req-multi-succ *)
Parameter PlayerCount : ℕ.

#[local] Infix "=?" := PlayerEqb (at level 70) : player_scope.

Axiom PlayerEqbEq :
  ∀ pl1 pl2, (PlayerEqb pl1 pl2) = true ↔ pl1 = pl2.

Axiom PlayerCyclicPermutation :
  ∀ pl1 pl2, exists! n, n < PlayerCount ∧ (PlayerNext ** n) pl1 = pl2.

Definition PlayerCountPositive : Prop :=
  0 < PlayerCount. (* req-multi *)


(* ========================================================================= *)
(* Helpers                                                                   *)
(* ========================================================================= *)

Section Player.
Open Scope player_scope.

Fixpoint ForallPlayersAux (fuel : ℕ) (pl plStart : Player) (cond : Player → bool) : bool :=
  match fuel with
  | O => true
  | S fuel' =>
      cond pl &&
      ((PlayerNext pl =? plStart) ||
      ForallPlayersAux fuel' (PlayerNext pl) plStart cond)
  end.

Definition ForallPlayers (cond : Player → bool) : bool :=
  ForallPlayersAux PlayerCount Host Host cond.

End Player.

Inductive Message : Type :=
  | GarbageMessage (n : ℕ) (* n is the number of garbage lines *)
  | GameoverMessage (* no payload, the message itself means gameover is true *)
  | DisconnectMessage. (* idem, means the sender is disconnected *)


(* ========================================================================= *)
(* Specification                                                             *)
(* ========================================================================= *)

(* For each state `s` and player `pl`, `s6 s pl`, `garbage s pl`, `target s pl`,
`gameoverView s pl`, `connectedView s pl` are local to pl.  `gameoverView s pl`
is what `pl` believes about the gameover state of other players. Idem for
connectedView about the network connection state of other players.

`messages` is different because it models the network, the environment the players
live in. Each player can send messages to each other players (technically a player
can send messages to herself but this never happens per NoSelfMessage invariant).
The connection is reliable: no message is lost and the message order is preserved.
`messages from to` is the sequence of messages from player `from` to player `to`.

`connected` is also not local to a player: it is the real state of the connectivity
of each player, not a view.
*)
Record State := mkState
  { s6            : Player → T6.State
  ; garbage       : Player → ℕ  (* received pending garbage *)
  ; target        : Player → Player
  ; gameoverView  : Player → Player → bool (* what each player knows about others *)
  ; connectedView : Player → Player → bool (* idem *)
  ; connected     : Player → bool (* real connectivity of each player; not a view *)
  ; messages      : Player → Player → list Message (* the messages passing through the network *)
  }.

Definition mg (s : State) (pl : Player) : Grid :=
  T6.mg (s6 s pl).

(* The real gameover status of a player; not a view. *)
Definition gameover (s : State) (pl : Player) : bool :=
  T6.gameover (s6 s pl).

Definition clearedLines (s : State) (pl : Player) : ℕ :=
  T6.clearedLines (s6 s pl).

Definition px (s : State) (pl : Player) : ℤ :=
  T6.px (s6 s pl).

Definition gy (s : State) (pl : Player) : ℤ :=
  T6.gy (s6 s pl).

Section Player.
Open Scope player_scope.

Definition UpdatePlayer (s : State) (pl : Player) (s6' : T6.State) : State :=
  {| s6 := λ pl2, if pl2 =? pl then s6' else s6 s pl2
  ;  garbage := garbage s (* unchanged *)
  ;  target := target s (* unchanged *)
  ;  gameoverView := λ obs obsd, (* only pl's view of herself can move, and only
                             if s6' made her gameover *)
       if (obs =? pl) && (obsd =? pl) then T6.gameover s6' else gameoverView s obs obsd
  ;  connectedView := connectedView s (* unchanged *)
  ;  connected := connected s (* unchanged *)
  ;  messages := messages s (* unchanged *)
  |}.

Definition UnchangedT7Part (s : State) (pl : Player) (s6' : T6.State) : State :=
  {| s6 := λ pl2, if pl2 =? pl then s6' else s6 s pl2
  ;  garbage := garbage s (* unchanged *)
  ;  target := target s (* unchanged *)
  ;  gameoverView := gameoverView s (* unchanged *)
  ;  connectedView := connectedView s (* unchanged *)
  ;  connected := connected s (* unchanged *)
  ;  messages := messages s (* unchanged *)
  |}.

(* True iff pl1 believes that pl2 is currently playing. *)
Definition PlayingView (s : State) (pl1 pl2 : Player) : bool :=
  ! gameoverView s pl1 pl2 && connectedView s pl1 pl2.

(* req-multi-winner. Reads pl's own view: a player decides she has won from
what she knows. ViewSound makes this sound (she is never wrong when she claims
it), only late (she may not know yet). *)
Definition WinnerMulti (s : State) (pl : Player) : bool :=
     (1 <? PlayerCount)
  (* all players are gameover, except pl, as far as pl knows *)
  && ForallPlayers (λ pl2, eqb (PlayingView s pl pl2) (pl2 =? pl)).

(* First successor of `pl` that is playing and not `self`.
Returns `self` when there is none (winner case of req-multi-target-nonself). *)
Fixpoint NextTargetAux (fuel : ℕ) (playing : Player → bool) (self pl : Player) : Player :=
  match fuel with
  | O => self
  | S fuel' =>
      let pl2 := PlayerNext pl in
      if playing pl2 && ! (pl2 =? self) then pl2
      else NextTargetAux fuel' playing self pl2
  end.

Definition NextTarget (playing : Player → bool) (self pl : Player) : Player :=
  NextTargetAux PlayerCount playing self pl.

Definition Init
    (bags : Player → ℕ → ℕ → Piece)
    (H : ∀ (pl : Player) (i : ℕ), T4.PieceSet (bags pl i)) : State :=
  let s6Init := λ pl, T6.Init (bags pl) (H pl) in
  {| s6 := s6Init
  ;  garbage := λ _, 0
  ;  target := λ pl, PlayerNext pl
  ;  gameoverView := λ obs obsd, (* nothing has been exchanged yet: each player knows only herself *)
       if obsd =? obs then T6.gameover (s6Init obsd) else false
  ;  connectedView := λ _ _, PlayerCount >? 1 (* not connected in single-player mode *)
  ;  connected := λ _, PlayerCount >? 1 (* idem *)
  ;  messages := λ _ _, []
  |}.

End Player.

Definition MovePiece (pl : Player) (dyx : ℤ × ℤ) (s : State) : option State :=
  if ! WinnerMulti s pl then
    option_map (UpdatePlayer s pl) (T6.MovePiece dyx (s6 s pl))
  else
    None.

Definition RotatePiece (pl : Player) (cw : bool) (s : State) : option State :=
  if ! WinnerMulti s pl then
    option_map (UpdatePlayer s pl) (T6.RotatePiece cw (s6 s pl))
  else
    None.

(* req-multi-garbage-gen *)
Definition GeneratedGarbage (clearedLines : ℕ) (perfectClear : bool) :=
  let c := clearedLines in
  let NormalGarbage := if c <? 4 then c - 1 else c in (* natural subtract >= 0 *)
  let SpecialGarbage := if perfectClear then 10 else 0 in
  NormalGarbage + SpecialGarbage.

Definition GenRemGarbage (garbage clearedLines : ℕ) (perfectClear : bool) : ℕ × ℕ :=
  let genGarbage := GeneratedGarbage clearedLines perfectClear in
  let remGarbage := garbage - genGarbage in (* req-multi-garbage-cancel *)
  (genGarbage, remGarbage).

Section Z.
Open Scope Z_scope.

Definition GarbageGrid (garbage : ℕ) (holes : ℤ → ℕ) (w : ℤ) : Grid :=
  {| L  := λ y x, (0 ≤? y <? garbage) && (0 ≤? x <? w) && ! (x =? holes y)
  ;  HW := (garbage, w)
  ;  YX := (0, 0)
  |}.

End Z.

Definition NewMainGridGameoverState (mg : Grid) (gameover : bool) (s6 : T6.State) : T6.State :=
  let s5 := T6.s5 s6 in
  let s4 := T5.s4 s5 in
  let s3 := T4.s3 s4 in
  let s2 := T3.s2 s3 in
  let s1 := T2.s1 s2 in
  let s1' := T1.NewMainGridGameoverState mg gameover s1 in
  let s2' := T2.UnchangedT2Part s2 s1' in
  let s3' := T3.UnchangedT3Part s3 s2' in
  let s4' := T4.UnchangedT4Part s4 s3' in
    (T6.UnchangedT6Part s6
      (T5.UpdateShadowY s5 s4')). (* was: T5.UnchangedT5Part s5 s4' *)

(* Holes are valid iff they are positioned inside a row. *)
Definition ValidHoles (f : ℤ → ℕ) : Prop :=
  ∀ i, 0 ≤ f i < W InitialMainGrid.

Section Player.
Open Scope player_scope.

(* Appends what pl emits when she fixes: at most one GarbageMessage, to her
target, and at most one GameoverMessage, to everyone else.
*)
Definition SendMessages (s : State) (pl : Player)
    (remGenGarbage : ℕ) (gameover' : bool) : Player → Player → list Message :=
  λ from to,
    if ! (from =? pl) then messages s from to (* only pl sends messages *)
    else if to =? pl then messages s from to (* no self messages *)
    else
      (* garbage first, then gameover *)
      let garbageMsg :=
        if (to =? target s pl) && (0 <? remGenGarbage)%nat
        then [GarbageMessage remGenGarbage] else [] in
      let gameoverMsg := if gameover' then [GameoverMessage] else [] in
      messages s from to ++ garbageMsg ++ gameoverMsg.

End Player.

(* Definitions used by FixPiece. In proofs, proper definitions are opaque by
default; they avoid the undisciplined expansion of let-expressions that can make
proof states very difficult to read. *)
Module FP.

Definition RemGenGarbage (s : State) (pl : Player) (s6' : T6.State) : ℕ :=
  let genGarbage := fst (GenRemGarbage (garbage s pl) (T6.clearedLines s6') (T6.perfectClear s6')) in
  (genGarbage - garbage s pl)%nat. (* req-multi-garbage-cancel *)

Definition Mg' (s : State) (pl : Player) (s6' : T6.State) (holes : ℤ → ℕ) : Grid :=
  let remGarbage := snd (GenRemGarbage (garbage s pl) (T6.clearedLines s6') (T6.perfectClear s6')) in
  let garbageGrid := GarbageGrid remGarbage holes (W InitialMainGrid) in
  let shiftedMg := T6.mg s6' ⊕ (remGarbage, 0) in
  (* mask has the same HW/YX as shiftedMg to avoid cropping, but its net effect
  is below its bbox: the empty blocks there are meaningful in the final union,
  screening off shiftedMg's content (whatever it may hold outside its own
  declared box) from garbageGrid's rows. *)
  let mask := {| L := λ y _, (remGarbage ≤? y)%Z; HW := HW shiftedMg; YX := YX shiftedMg |} in
  garbageGrid ∪ (shiftedMg ∩ mask). (* req-multi-garbage-materialize *)

Definition CroppedMg' (s : State) (pl : Player) (s6' : T6.State) (holes : ℤ → ℕ) : Grid :=
  (Mg' s pl s6' holes) ∩ Full (T6.mg s6').

Definition Gameover' (s : State) (pl : Player) (s6' : T6.State) (holes : ℤ → ℕ) : bool :=
  let croppedMg' := CroppedMg' s pl s6' holes in
  T6.gameover s6' || (* T1 forbidden zone intersect *)
  ((Mg' s pl s6' holes) ⊈ croppedMg') || (* req-multi-gameover: out-of-box occupied blocks *)
  (ForbiddenGrid ∩ croppedMg' ⊈ ∅). (* forbidden zone intersect on mg with garbage *)

Definition GameoverView' (s : State) (pl : Player) (s6' : T6.State) (holes : ℤ → ℕ) : Player → bool :=
  λ pl2, if (pl2 =? pl)%player then
    Gameover' s pl s6' holes
  else
    gameoverView s pl pl2.

Definition PlayingView' (s : State) (pl : Player) (s6' : T6.State) (holes : ℤ → ℕ) : Player → bool :=
  λ pl2, ! (GameoverView' s pl s6' holes) pl2 && connectedView s pl pl2.

End FP.

Section Player.
Open Scope player_scope.

Definition FixPiece (pl : Player)
    (holes : ℤ → ℕ) (H1 : ValidHoles holes)
    (bagNew : ℕ → Piece) (H2 : T4.PieceSet bagNew)
    (s : State) : option State :=
  if ! WinnerMulti s pl then
    option_map
      (λ s6',
        if (PlayerCount =? 1)%nat then
          UpdatePlayer s pl s6'
        else
          (* If here player pl is gameover, she has fixed a piece in the forbidden zone.
          This means no line has been cleared. Therefore no garbage is generated and in
          the following mg' = mg, resulting in a no-op from the garbage point of view. *)
          let gameover' := FP.Gameover' s pl s6' holes in
          let remGenGarbage := FP.RemGenGarbage s pl s6' in
          {| s6 := λ pl2,
              if pl2 =? pl then
                NewMainGridGameoverState (FP.CroppedMg' s pl s6' holes) gameover' s6'
              else
                s6 s pl2
          ;  garbage := λ pl2,
              if pl2 =? pl then
                0 (* remaining garbage is consumed by being materialized *)
              else
                garbage s pl2 (* unchanged: the target is credited on delivery,
                              not here (see ReceiveMessage) *)
          ;  target := λ pl2,
              (* Only pl's own target may move here. The targets of the players
              who were aiming at pl cannot: they do not know yet that pl died.
              They redirect when they receive the GameoverMessage. *)
              if (pl2 =? pl) && (0 <? remGenGarbage)%nat && ! gameover' then
                (* req-multi-garbage-send: the target becomes its first
                successor that is not gameover *)
                NextTarget (FP.PlayingView' s pl s6' holes) pl (target s pl)
              else
                target s pl2
          ;  gameoverView := λ obs obsd,
              if (obs =? pl) && (obsd =? pl) then gameover' (* SelfViewAccurate *)
              else gameoverView s obs obsd
          ;  connectedView := connectedView s
          ;  connected := connected s
          ;  messages :=
               (* Only when pl is really connected (not just believing it is) can the
               messages be effectively sent, hence connected instead of connectedView below. *)
               if connected s pl then SendMessages s pl remGenGarbage gameover'
               else messages s
          |})
      (T6.FixPiece bagNew H2 (s6 s pl))
  else
    None.

Definition FallStep (pl : Player)
    (holes : ℤ → ℕ) (Hholes : ValidHoles holes)
    (bagNew : ℕ → Piece)
    (H : T4.PieceSet bagNew) (s : State) : option State :=
  if ! WinnerMulti s pl then
    match MovePiece pl (-1, 0)%Z s with
    | Some s' => Some s'
    | None    => FixPiece pl holes Hholes bagNew H s
    end
  else
    None.

Definition HoldPiece (pl : Player)
    (holes : ℤ → ℕ) (Hholes : ValidHoles holes)
    (bagNew : ℕ → Piece) (H : T4.PieceSet bagNew) (s : State) : option State :=
  if ! WinnerMulti s pl then
    option_map (UpdatePlayer s pl) (T6.HoldPiece bagNew H (s6 s pl))
  else
    None.

Definition NewPieceYXState (pyxNew : ℤ × ℤ) (pl : Player) (s : State) : State :=
  UnchangedT7Part s pl (T6.NewPieceYXState pyxNew (s6 s pl)).

Definition DropPiece (pl : Player)
    (holes : ℤ → ℕ) (H1 : ValidHoles holes)
    (bagNew : ℕ → Piece) (H2 : T4.PieceSet bagNew) (s : State) : option State :=
  FixPiece pl holes H1 bagNew H2 (NewPieceYXState (gy s pl, px s pl) pl s).

Definition RotateKickPiece (pl : Player) (cw : bool) (s : State) : option State :=
  if ! WinnerMulti s pl then
    option_map (UpdatePlayer s pl) (T6.RotateKickPiece cw (s6 s pl))
  else
    None.

(*
Delivery of the message at the head of the queue from `from` to `pl`.

Not gated on WinnerMulti nor on pl being alive: a gameover player keeps
draining her queues. Garbage delivered to a gameover player sits inert
(she can never fix again, so it is never read), and gameover messages are
what lets her learn the game is over.
*)
Definition ReceiveMessage (pl from : Player) (s : State) : option State :=
  if connected s pl then
    match messages s from pl with
    | [] => None
    | m :: rest =>
        let messages' := λ f t, if (f =? from) && (t =? pl) then rest else messages s f t in
        let view' := λ pl2, if pl2 =? from then false else PlayingView s pl pl2 in
        match m with
        | GarbageMessage n =>
            Some
              {| s6 := s6 s
              ;  garbage := λ pl2, if pl2 =? pl then (garbage s pl2 + n)%nat else garbage s pl2
              ;  target := target s
              ;  gameoverView := gameoverView s
              ;  connectedView := connectedView s
              ;  connected := connected s
              ;  messages := messages'
              |}
        | GameoverMessage =>
            Some
              {| s6 := s6 s
              ;  garbage := garbage s
              ;  target := λ pl2,
                  (* pl redirects only if she was aiming at the player who died *)
                  if (pl2 =? pl) && (target s pl =? from) then NextTarget view' pl from
                  else target s pl2
              ;  gameoverView := λ obs obsd,
                  if (obs =? pl) && (obsd =? from) then true else gameoverView s obs obsd
              ;  connectedView := connectedView s
              ;  connected := connected s
              ;  messages := messages'
              |}
        | DisconnectMessage =>
            Some
              {| s6 := s6 s
              ;  garbage := garbage s
              ;  target := λ pl2, (* same as gameover: redirect target *)
                  if (pl2 =? pl) && (target s pl =? from) then NextTarget view' pl from
                  else target s pl2
              ;  gameoverView := gameoverView s
              ;  connectedView := λ pl1 pl2,
                  if (pl1 =? pl) && (pl2 =? from) then false
                  else connectedView s pl1 pl2
              ;  connected := connected s
              ;  messages := messages'
              |}
        end
    end
  else
    None.

(* connectedView is not updated here because the player may take some time to
notice she is disconnected (see NoticeDisconnection).

One edge case worth noting: a player A can temporarily (see NoticeDisconnection)
believe she is the winner because the winner computation is based on the local view,
including the local connected view. But since the player is really disconnected, she
cannot send or receive messages, so she has no impact on other players. Meanwhile,
other player are notified that A is disconnected. So in the end, the only impact is
completely local to A.

Note: connectedView is also used to determine the next target after garbage has been
sent. But a player cannot be her own target, so A wrongly believing she is connected
is harmless here.
*)
Definition DisconnectPlayer (pl : Player) (s : State) : option State :=
  if connected s pl then
    Some
      {| s6 := s6 s
      ;  garbage := garbage s
      ;  target := target s
      ;  gameoverView := gameoverView s
      ;  connectedView := connectedView s
      ;  connected := λ pl1, (* if the host is disconnected, everyone is *)
           if (pl =? Host) || (pl1 =? pl) then false else connected s pl1
      ;  messages := λ from to, (* no message can be sent if the host is disconnected *)
           if ! (pl =? Host) && (from =? pl) && ! (to =? pl) then (* host sends to other players *)
             messages s from to ++ [DisconnectMessage]
           else
             messages s from to
      |}
  else
    None.

(* A disconnected player notices she is disconnected and updates her view. *)
Definition NoticeDisconnection (pl : Player) (s : State) : option State :=
  if ! connected s pl && connectedView s pl pl then
    Some
      {| s6 := s6 s
      ;  garbage := garbage s
      ;  target := target s
      ;  gameoverView := gameoverView s
      ;  connectedView := λ pl1 pl2,
           if (pl1 =? pl) && (pl2 =? pl) then false else connectedView s pl1 pl2
      ;  connected := connected s
      ;  messages := messages s
      |}
  else
    None.

End Player.

Inductive Event :=
  | Move (dyx : ℤ × ℤ) (* OK *)
  | Rotate (cw : bool) (* OK *)
  | Fix (holes : ℤ → ℕ) (H1 : ValidHoles holes)
      (bagNew : ℕ → Piece) (H2 : T4.PieceSet bagNew)
  | Fall (holes : ℤ → ℕ) (H1 : ValidHoles holes) (* OK *)
      (bagNew : ℕ → Piece) (H2 : T4.PieceSet bagNew)
  | Hold (holes : ℤ → ℕ) (H1 : ValidHoles holes) (* OK *)
      (bagNew : ℕ → Piece) (H2 : T4.PieceSet bagNew)
  | Drop (holes : ℤ → ℕ) (H1 : ValidHoles holes)
      (bagNew : ℕ → Piece) (H2 : T4.PieceSet bagNew)
  | RotateKick (cw : bool) (* OK *)
  | Receive (from : Player) (* OK *)
  | Disconnect (* OK *)
  | Notice (* OK *)
  | Stutter. (* OK *)

Definition Next (pl : Player) (e : Event) (s : State) : option State :=
  match e with
  | Move dyx                => MovePiece pl dyx s
  | Rotate cw               => RotatePiece pl cw s
  | Fix holes H1 bagNew H2  => FixPiece pl holes H1 bagNew H2 s
  | Fall holes H1 bagNew H2 => FallStep pl holes H1 bagNew H2 s
  | Hold holes H1 bagNew H2 => HoldPiece pl holes H1 bagNew H2 s
  | Drop holes H1 bagNew H2 => DropPiece pl holes H1 bagNew H2 s
  | RotateKick cw           => RotateKickPiece pl cw s
  | Receive from            => ReceiveMessage pl from s
  | Disconnect              => DisconnectPlayer pl s
  | Notice                  => NoticeDisconnection pl s
  | Stutter                 => Some s
  end.


(* ========================================================================= *)
(* State invariants                                                          *)
(* ========================================================================= *)

Section Player.
Open Scope player_scope.

(* The truth of who is playing, as opposed to PlayingView. *)
Definition Playing (s : State) (pl : Player) : bool :=
  ! gameover s pl && connected s pl.

(* req-multi-winner. A statement about the system, not an observation: it
reads the truth, not any player's view. *)
Definition NoWinner (s : State) : Prop :=
  ∃ pl1 pl2, pl1 ≠ pl2 ∧ Playing s pl1 = true ∧ Playing s pl2 = true.

(* No connectedView clause because a player may not notice immediately
she is disconnected (see DisconnectPlayer and NoticeDisconnection). *)
Definition SelfViewAccurate (s : State) : Prop := ∀ pl,
  gameoverView s pl pl = gameover s pl.

(* Views lag the truth, they never lead it. This is what makes staleness safe
rather than arbitrary, and it is what makes WinnerMulti sound: if pl believes
everyone else is gameover then everyone else really is, so she really has won.
Only the converse lags: she may have won without knowing it yet. *)
Definition ViewSound (s : State) : Prop := ∀ pl pl2,
    (gameoverView s pl pl2 = true → gameover s pl2 = true)
  ∧ (connectedView s pl pl2 = false → connected s pl2 = false).

(* Messages do not lie. This is what makes ViewSound inductive: delivery needs
the truth to hold at pop time, and GameoverMonotone carries it from the send. *)
Definition MessageSound (s : State) : Prop := ∀ from to,
    (In GameoverMessage (messages s from to) → gameover s from = true)
  ∧ (In DisconnectMessage (messages s from to) → connected s from = false).

(* A player never messages herself. *)
Definition NoSelfMessage (s : State) : Prop :=
  ∀ pl, messages s pl pl = [].

(* The shape of the sequence of messages between two players A and B is: an
arbitrary number of garbage messages, then a gameover message if A is gameover,
then a disconnect message if A is disconnected. The key point is that if both
events occur, gameover is always before disconnection. This is because gameover
message is sent on FixPiece and FixPiece cannot occur if disconnected (because
the player is not playing anymore, see WinnerMulti and PlayingView). *)
Definition LastMessagesGameoverDisconnect (s : State) : Prop :=
  ∀ from to : Player, from ≠ to →
    ∃ (ns : list ℕ) (b1 b2 : bool), (* b1/b2 make GameoverMessage/DisconnectMessage optional  *)
      messages s from to = map GarbageMessage ns
        ++ (if b1 then [GameoverMessage] else [])
        ++ (if b2 then [DisconnectMessage] else []).

(* req-multi-target-nonself. Holds by construction of NextTarget, which never
returns `self` unless there is nobody else alive to return (and under NoWinner
there always is). *)
Definition TargetNotSelf (s : State) : Prop :=
  PlayerCount > 1 → (* for clarity only; redundant because implied by NoWinner *)
  NoWinner s →
  ∀ pl, target s pl ≠ pl.

(* View-relative. pl's target may be truly gameover/disconnected while pl's
GameoverMessage/DisconnectMessage is still in flight. That window is precisely
what the network model exists to admit. Garbage sent into it lands on a player
who can never read it (see ReceiveMessage), so it is inert. *)
Definition TargetPlaying (s : State) : Prop :=
  PlayerCount > 1 → (* for clarity only; redundant because implied by NoWinner *)
  NoWinner s →
  ∀ pl, PlayingView s pl (target s pl) = true.

(* Forbidden grid intersection is not the only cause of gameover anymore:
another cause is an overflow following a garbage materialization. However, the
state keeps no trace of an overflow because the rest of the model doesn't need
it. Adding this cause to the state seems artificial, so we prefer weaken
T1.gameover by replacing the equivalence by a mere implication. *)
Definition Gameover (pl : Player) (s : State) : Prop :=
  (ForbiddenGrid ∩ mg s pl) ⊈ ∅ = true → gameover s pl = true.

Definition S6Correct (s : State) : Prop :=
  ∀ pl : Player,
      T6.CorrectWithoutGameover (s6 s pl)
    ∧ Gameover pl s.

Definition Correct (s : State) : Prop :=
    S6Correct s
  ∧ SelfViewAccurate s (* OK *)
  ∧ ViewSound s (* OK *)
  ∧ MessageSound s (* OK *)
  ∧ NoSelfMessage s (* OK *)
  ∧ LastMessagesGameoverDisconnect s (* OK *)
  ∧ TargetNotSelf s (* OK *)
  ∧ TargetPlaying s. (* OK *)

End Player.


(* ========================================================================= *)
(* Step invariants                                                           *)
(* ========================================================================= *)

(* Messages are the only interaction mechanism between players, i.e.
   an action from one player can never touch another player's own game. *)
Definition OtherS6Unchanged (s s' : State) : Prop := ∀ e pl1 pl2
  (H1 : Next pl1 e s = Some s')
  (H2 : pl2 ≠ pl1),
  s6 s' pl2 = s6 s pl2.

(* Once a player is gameover, this cannot be undone. *)
Definition GameoverMonotone (s s' : State) : Prop := ∀ e pl1 pl2
  (H1 : Next pl1 e s = Some s')
  (H2 : gameover s pl2 = true),
  gameover s' pl2 = true.

(* Same, on views: nobody ever un-learns a death. This is what makes
ReceiveMessage idempotent under duplicate or late delivery. *)
Definition GameoverViewMonotone (s s' : State) : Prop := ∀ e pl1 pl2 pl3
  (H1 : Next pl1 e s = Some s')
  (H2 : gameoverView s pl2 pl3 = true),
  gameoverView s' pl2 pl3 = true.

Definition DisconnectedMonotone (s s' : State) : Prop := ∀ e pl1 pl2
  (H1 : Next pl1 e s = Some s')
  (H2 : connected s pl2 = false),
  connected s' pl2 = false.

Definition DisconnectedViewMonotone (s s' : State) : Prop := ∀ e pl1 pl2 pl3
  (H1 : Next pl1 e s = Some s')
  (H2 : connectedView s pl2 pl3 = false),
  connectedView s' pl2 pl3 = false.

Definition CorrectStep (pl : Player) (s s' : State) : Prop :=
    T6.CorrectStep (s6 s pl) (s6 s' pl)
  ∧ OtherS6Unchanged s s'
  ∧ GameoverMonotone s s'
  ∧ GameoverViewMonotone s s'
  ∧ DisconnectedMonotone s s'
  ∧ DisconnectedViewMonotone s s'.


(* ========================================================================= *)
(* Refinement                                                                *)
(* ========================================================================= *)

(* Define the refinement mapping f with its event component and its
   state component. *)

(* Event component. Partial: Receive has no T6 counterpart. *)
Definition fₑ (e7 : T7.Event) : T6.Event :=
  match e7 with
  | Move dyx           => T6.Event5 (T5.Event4 (T4.Move dyx))
  | Rotate cw          => T6.Event5 (T5.Event4 (T4.Rotate cw))
  | Fix  _ _ bagNew H2 => T6.Event5 (T5.Event4 (T4.Fix bagNew H2))
  | Fall _ _ bagNew H2 => T6.Event5 (T5.Event4 (T4.Fall bagNew H2))
  | Hold _ _ bagNew H2 => T6.Event5 (T5.Event4 (T4.Hold bagNew H2))
  | Drop _ _ bagNew H2 => T6.Event5 (T5.Drop bagNew H2)
  | RotateKick cw      => T6.RotateKick cw
  | Receive _ | Disconnect | Notice | Stutter => T6.Event5 (T5.Event4 T4.Stutter)
  end.

(* State component *)
Definition fₛ (pl : Player) (s7 : T7.State) : T6.State :=
  s6 s7 pl.

(*
For T6 refinement to hold, this diagram must commute:
            e6
      s6    →    s6'
fₛ pl ↑     ⇑fₑ  ↑ fₛ pl
      s7    →    s7'
            e7
*)

Section Nat.
Open Scope nat_scope.

Definition NoRemGarbage (pl : Player)
    (bagNew : ℕ → Piece) (H2 : T4.PieceSet bagNew) (s : State) : Prop :=
  match T6.FixPiece bagNew H2 (s6 s pl) with
  | Some s6' => snd (GenRemGarbage (garbage s pl) (T6.clearedLines s6') (T6.perfectClear s6')) = 0
  | None => True
  end.

Definition NoMaterializedGarbage (pl : Player)
  (bagNew : ℕ → Piece) (H2 : T4.PieceSet bagNew) (s : State) : Prop :=
    PlayerCount = 1
  ∨ NoRemGarbage pl bagNew H2 s.

End Nat.

Definition T7RefinesT6 : Prop :=
    (∀ pl bags HbagNew,
      fₛ pl (T7.Init bags HbagNew) = T6.Init (bags pl) (HbagNew pl))
  ∧ (∀ pl e7 e6 s7 s7'
      (H1 : Correct s7)
      (H2 : Next pl e7 s7 = Some s7')
      (H3 : fₑ e7 = e6)
      (H4 : ∀ holes Hholes bagNew HbagNew,
        e7 = Fix holes Hholes bagNew HbagNew →
        NoMaterializedGarbage pl bagNew HbagNew s7)
      (H5 : ∀ holes Hholes bagNew HbagNew,
        e7 = Drop holes Hholes bagNew HbagNew →
        NoMaterializedGarbage pl bagNew HbagNew (NewPieceYXState (gy s7 pl, px s7 pl) pl s7)),
      T6.Next e6 (fₛ pl s7) = Some (fₛ pl s7')).
