# proofs.md — refinement proof, `t6/model.js ⊨ T6.v`

Delta over `t5/proofs.md`. `T6.v` refines `T5.v` via `fₑ = id` and `fₛ = id` — both
identities, since `T6.State = T5.State` (a type alias, `T6.v`'s `Definition State :=
T5.State`, not a new
record). The refinement holds only for `Event5` events (`T6.v`'s own note);
`RotateKick` has no refinement claim, the same shape as T3's exclusion of `Hold` and
T5's exclusion of `Drop`.

## 1. Scope

Safety only. `RotateKick`'s exclusion is structural, stated by `T6.v` itself.

## 2. State mapping α

`α_T6 = α_T5`, unchanged — there is no new field to map. This is the only model in the
chain so far where α is literally the identity on the *representation*, not just on
the abstract state: `T6.Machine` is a JS subclass of `T5Eng.Machine`, not a wrapper
with a new field, so a T6.Machine instance and the T5.Machine instance it *is* share
every field directly. No projection lemma is needed for `movePiece`/`rotatePiece`/
`fixPiece`/`fallStep`/`holdPiece`/`dropPiece` beyond "T6.Machine inherits T5.Machine's
implementation unchanged" — literally true by JS inheritance, not argued per method.

## 3. `rotateKickPiece` — no-use, full fresh argument

**Guard / exclusivity.** `T6.RotateKickPiece`'s guard is a conjunction,
`(! gameover s) && (! plainRotFires)`, where `plainRotFires` is `T6.v`'s
`let plainRotFires := match T5.RotatePiece clockwise s with Some _ => true |
None => false end in`. `L-canRotatePiece` (`t1/proofs.md`) establishes
`canRotatePiece(cw, s) ⟺ rotatePiece(cw)` would fire on a machine in state
`s` — i.e. `canRotatePiece(cw, s) ⟺ plainRotFires`, not `⟺` the full
conjunction: `canRotatePiece`'s own definition (`!s.gameover &&
valid(...)`) folds a `!gameover` check into computing `plainRotFires`
itself, but that's a fact about *how `plainRotFires` gets computed*, not a
restatement of `T6.v`'s *outer* `!gameover` conjunct — `gameover ⟹
!plainRotFires` (rotation can't fire under gameover, so `plainRotFires` is
already false there), not the reverse, so `!plainRotFires` does not entail
`!gameover`. Concretely: `T1Eng.canRotatePiece(cw, s1)` is single-valued —
`rotateKickPiece` has no separate check for "the acting player is already
gameover," unlike `T6.v`'s explicit outer conjunct.

This does not cause a divergence, but the reason needs stating rather than
assumed: `!T1Eng.canRotatePiece(cw, s1)` is true both when rotation is
genuinely blocked (`T6.v`'s intended case) *and* when `s.gameover` is
already `true` (a case `T6.v`'s guard would exclude outright, before ever
reaching `plainRotFires`). In the second case, JS still enters the kick-
attempt branch below — but every `this.rotatePiece(cw)` call inside it
carries `T1.RotatePiece`'s own guard, `!(!this.gameover &&
valid(...))`-gated (`t1/model.js`), so both attempts fail immediately
without mutating `s1.pr`, and the kick-attempts bullet below (mutate-then-
restore) already establishes that `s1.px` is restored to `origPx`
regardless of *why* `rotatePiece` rejected. So both branches — "blocked,
not gameover" and "gameover" — end at the identical observable outcome
JS produces either way: `fired = false`, `s1` unchanged. `T6.v`'s outer
`!gameover` conjunct is real in the specification but provably redundant
given `T5.RotatePiece`'s own guard and `NewPieceYXState`'s preservation of
`gameover` (`t1/model.js`'s `newPieceYXState`: `gameover: s.gameover`,
unconditionally carried through) — `rotateKickPiece`'s single check is
sound *because of* that redundancy, not in spite of a gap in it. When
`canRotatePiece` holds (plain rotation would fire), `rotateKickPiece`
returns `false` and touches nothing — matching `RotateKickPiece`'s own
`else None` branch, the one case (`plainRotFires = true`) where the
conjunction is false regardless of `gameover`.

**Kick attempts.** When `T1Eng.canRotatePiece` is false, the method tries `px - 1` then
`px + 1`, in each case setting `s1.px` and calling `this.rotatePiece(cw)` (T5's own,
inherited method — not reimplemented). Two things to show:

- **The call sequence matches `T6.v`'s left-then-right, both relative to the
  *original* position.** `T6.v`'s left branch calls `T5.RotatePiece clockwise
  (T5.NewPieceYXState (py s) (px s - 1) s)` — i.e. `px s - 1`, the *original* `s`'s
  `px`, not a running total. The JS body computes `origPx = s1.px` once, before
  either attempt, and uses `origPx - 1`/`origPx + 1` for the two tries — so the
  right attempt is relative to the original position even if the left attempt was
  tried (and failed) first, matching `T6.v`'s own right branch reading from `s`,
  not from the (failed) left-shifted intermediate.
- **Mutating `s1.px` before calling `rotatePiece` is sound here, unlike a
  peek-then-commit hazard.** `t4/proofs.md` §4 required deferring a mutation until
  success was confirmed because there was no way to undo a consumed preview piece
  cheaply. Here, `px` is a plain scalar: if `this.rotatePiece(cw)` rejects (its own
  guard fails, touching nothing else per the established stuttering-step property,
  and regardless of which conjunct of that guard — `gameover` or `valid` — is what
  actually failed), the only stray effect is `s1.px` sitting at the tried value,
  which the method explicitly restores (`s1.px = origPx`) before returning `false`.
  No accumulated state, no side effect beyond the one field being tried, unlike a
  bag draw.
- **`gy` refresh is inherited, not re-derived.** A successful `rotateKickPiece` call
  ends by having called `this.rotatePiece(cw)` (T5's own), whose own `gy`-refresh
  obligation (`t5/proofs.md` §3) already applies — `rotateKickPiece` needs no
  separate argument for this, precisely because it reuses `rotatePiece` for the
  actual mutation rather than reimplementing rotation+relocation raw.

**No new invariant.** `T6.Correct := T5.Correct` (`T6.v`'s `Definition Correct (s :
State) : Prop := T5.Correct s`, unchanged) —
`rotateKickPiece`'s only path to a non-trivial post-state is via a successful
`this.rotatePiece(cw)` call, already covered by `t5/proofs.md` §3; the exclusivity
and restore-on-failure paths leave the state exactly as it was, requiring nothing of
`T5.Correct` beyond what already held.

## 4. Cap soundness — not applicable

`rotateKickPiece` introduces no new arithmetic and touches no capped accumulator.

## 5. `Init` and every other action

Both are `T5.v`'s own, unchanged (`T6.v` defines no new `Init`, and `Event5`'s
`Next` case is a direct forward, `T6.v`'s `| Event5 e5 => NextT5Event e5 s`
clause). `Machine`'s constructor is
inherited from `T5Eng.Machine` verbatim — no new field to initialize (`T6.v`'s own
comment on `State`'s definition: "No new state fields").

## 6. Summary

- **`movePiece`/`rotatePiece`/`fixPiece`/`fallStep`/`holdPiece`/`dropPiece`** —
  inherited unchanged from `T5Eng.Machine`; `t5/proofs.md` applies verbatim, no new
  argument (§2).
- **`rotateKickPiece`** — no-use, full fresh argument: exclusivity via
  `canRotatePiece` (imported from `t1/proofs.md`'s `L-canRotatePiece`), kick
  attempts relative to the original position, sound mutate-then-restore (unlike
  T4's `fixPiece`, since `px` has no accumulated side effect to undo), `gy`-refresh
  inherited from `rotatePiece` (§3).
