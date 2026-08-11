# proofs.md — refinement proof, `t3/model.js ⊨ T3.v`

`T3.v` refines `T2.v` via `f = (fₑ, fₛ)` with `fₑ = id` on
`T2.Event` and `fₛ = s2` (state projection) — but **only for `Event2` events**
(T3.v's `T3RefinesT2` definition quantifies only over `T2.Event`, wrapped by
`Event2`). `Hold` has no refinement claim in `T3.v` itself; its invariant
preservation is argued fresh in §5.

## 1. Scope

Safety only (no liveness). Additionally — not merely "out of controller
scope" the way fall-speed/banners are, but a structural fact stated by the
model: `Hold` is excluded from the refinement diagram (T3.v's own header comment
and its `T3RefinesT2` definition), so nothing about it is inherited from
`T1Proofs.v`/`T2Proofs.v`.

## 2. State mapping α

`α_T3(js) = { s2 := α_T2(js.s2); hold := js.hold; swapped := js.swapped }` — apply
`t2/proofs.md`'s `α_T2` to the embedded inner machine; `hold` (`Piece | null`) and
`swapped` (`boolean`) map directly, no coercion.

## 3. `movePiece`, `rotatePiece` — full-use transfer

`T3.MovePiece`/`RotatePiece` are `option_map (UnchangedT3Part s)` over the
corresponding `T2` call and nothing else (T3.v's `MovePiece`/`RotatePiece`
definitions) — `hold`/`swapped` are
left alone, not even re-copied with new logic. JS: `this.s2.movePiece(dy,dx)` /
`this.s2.rotatePiece(cw)`, one-line delegations. `t2/proofs.md`'s own action lemmas
transfer unchanged; T3's obligation is only "the inner machine received the identical
call, and `hold`/`swapped` are untouched" — true by inspection (§4-T3b).

## 4. `fixPiece` — partial-use transfer

`T3.FixPiece` delegates to `T2.FixPiece`, then additionally sets `swapped := false`
(req-hold-limit, T3.v's `FixPiece` definition); `hold` is copied unchanged. JS:
```
const fired = this.s2.fixPiece(pNew);
if (!fired) return false;
this.swapped = false;
```
`t2/proofs.md`'s `fixPiece` argument transfers for the `s2` part (guard-fail →
stutter; guard-hold → field match). The only new obligation is `this.swapped = false`
matching `T3.FixPiece`'s explicit field — trivial, no ordering hazard (`swapped`'s
write doesn't read any value the delegation touched).

## 5. `holdPiece` — no-use, full fresh argument

**Guard.** `!this.gameover && !this.swapped` — `this.gameover` is the getter
(`get gameover() { return this.s2.gameover; }`), definitionally `T3.v`'s own
`gameover` helper (`T1.gameover (s1 (s2 s))`); `this.swapped` is
a plain field. Matches T3.v's own `HoldPiece` guard, `! (gameover s) && ! (swapped s)`, exactly.

**`T1.Correct (s1 (s2 s))` preservation.** `NewPieceState` (`T1.v`) only rewrites
`p, py, px, pr`; `mg`, `gameover`, `clearedLines` pass through unchanged (confirmed
field-by-field in `t1/model.js`'s `newPieceState`, and by `t1/proofs.md`'s
`L-newPieceState`). Checking `T1.v`'s five `Correct` conjuncts
against that:
- **`TypeOK`, `Gameover`, `NoFullLine` — trivial.** All three depend only on `mg`
  and/or `gameover`, both untouched.
- **`PieceOccupiedInsideBounds`, `PieceOnFreeBlocks` — need `AxiomsRotGrid`.** Both
  depend on `p, py, px, pr`, which are rewritten to `p2, InitialY p2, InitialX p2, 0`.
  `AxiomsRotGrid`'s `FullyContainedIn (RotGrid p 0) (InitialY p) (InitialX p)
  ForbiddenGrid FY FX` (stated `∀ p : Piece`, so it applies to `p2`
  regardless of which piece that is) combined with `AxiomsForbiddenGrid`'s
  `BBoxInsideBBox ForbiddenGrid FY FX InitialMainGrid 0 0` is the
  *same* lemma `T1Proofs.v` already uses for `Init`'s and `FixPiece`'s spawn — this
  is a re-invocation here, not a re-derivation: the fresh piece `p2` at its spawn
  position occupies only cells inside the forbidden zone's occupied set; combined
  with the pre-condition `¬gameover s` (i.e. `mg` has no occupied cell anywhere the
  forbidden zone is occupied, by `Gameover`'s biconditional), the fresh piece cannot
  intersect `mg` and is fully inside its bounds.

**`LevelCorrect (s2 s)` preservation — trivial.** `T3.v`'s `HoldPiece` builds the new
`s2` via `T2.UnchangedT2Part s2_ (...)`: `score`, `level`, `combo`,
`perfectClear`, `totalClearedLines` are copied unchanged. Both sides of
`LevelCorrect`'s equation are literally the same value before and after — no new
argument beyond "field untouched," matching `t2/proofs.md`'s own treatment of fields
`UnchangedT2Part` leaves alone.

**`SwappedImplyHoldSome` preservation** (`swapped s = true → hold s ≠ None`).
`holdPiece` sets `this.hold = oldP` and `this.swapped = true` in the same call,
`oldP` always being a concrete `Piece` value (`this.s2.s1.p`, never `null`) — so
whenever this branch makes `swapped` true, `hold` is simultaneously non-`null`.
Every other action either leaves both fields untouched (`movePiece`/`rotatePiece`)
or sets `swapped := false` (`fixPiece`), which satisfies the implication vacuously
regardless of `hold`.

**`GameoverImplyNotSwapped` preservation** (`gameover s = true → swapped s = false`).
`holdPiece`'s guard requires `¬gameover` to fire at all, and `gameover` is untouched
by `NewPieceState` — so this action can never produce a state with `gameover = true`.
The only action that *can* set `gameover := true` is `fixPiece` (inherited from
`T1.FixPiece`, unaffected by T3), which simultaneously sets `swapped := false` in the
same call (§4) — so the implication holds at every state reachable via a fix, and
vacuously everywhere `swapped` is left `false` or untouched-false by the other
actions.

**`HoldMonotone`** (`hold s ≠ None → hold s' ≠ None` for any firing transition).
`hold` is written only by `holdPiece`, always to `Some(oldP)` — a concrete value,
never `null`. Every other action leaves it untouched. Trivial case split over the
five T3 actions.

**Ordering (skill §4b).** `this.s2.s1.p` is read into `oldP` **before** `newS1`'s
fields are written into `this.s2.s1` — the one hazard in this method, mirroring
`T3.v`'s `hold := Some (p s)` reading the pre-state `p s`, not the value
`NewPieceState` just computed. `newS1` is computed from `this.s2.s1`'s pre-write
values (`newPieceState(p2, this.s2.s1)` is called before any of the seven
`this.s2.s1.<field> = …` assignments), so no field is read after being overwritten.

## 6. `fallStep` — disjoint-guard sequencing (skill §6.6)

Unaffected by T3: T3.v's `FallStep` definition has the identical shape as
T1/T2's, built from `T3.MovePiece (-1) 0` and `T3.FixPiece p_new`, both already
covered (§3, §4). The same mutual-exclusivity argument (`t1/proofs.md` §10,
`t2/proofs.md` §4) transfers unchanged.

## 7. Cap soundness — not applicable

`Hold` introduces no new arithmetic and touches none of the three capped
accumulators (`score`, `combo`, `totalClearedLines`) — confirmed above,
`T2.UnchangedT2Part` leaves them untouched. No new cap obligation beyond
`t2/proofs.md` §5, which already covers every path that touches them (`fixPiece`,
unaffected by T3).

## 8. `Init`

`constructor(p)` ≙ `Init p` (`T3.v`), field-by-field:

| field | JS | Rocq (`Init p`) |
|---|---|---|
| `s2` | `new T2Eng.Machine(p)` | `T2.Init p` — by `t2/proofs.md` §7 |
| `hold` | `null` | `None` |
| `swapped` | `false` | `false` |

`checkAxioms` is `T2Eng.checkAxioms` unchanged (T3 introduces no new abstract
parameters or axioms — T3.v's own "No new parameter" comment).

## 9. Each action — summary

- **`movePiece(dy,dx)`** — one-line delegation, full use (§3).
- **`rotatePiece(cw)`** — one-line delegation, full use (§3).
- **`fixPiece(pNew)`** — partial use: delegate, then `swapped := false` (§4).
- **`fallStep(pNew)`** — disjoint-guard sequencing (§6).
- **`holdPiece(pNew)`** — no-use, full fresh argument (§5): guard correspondence,
  `T1.Correct`/`LevelCorrect` preservation, the two new T3 invariants, `HoldMonotone`,
  and the read-before-write ordering.
