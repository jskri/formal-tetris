# proofs.md — refinement proof, `t4/model.js ⊨ T4.v`

`T4.v` refines `T3.v` via `fₛ = s3` and a **state-dependent** `fₑ`: every one of
T4's five events maps to a T3 event, but which T3 event depends on `next s 0`,
read off the pre-transition state.

## 1. Scope

Safety only. `RefineT3` (T4.v's `RefineT3` definition) has exactly two conjuncts —
`InitRefineT3` and `NextRefineT3` — no `None`-preservation clause. This is
deliberate, not an omission: a forward-simulation safety argument only needs
start/step conditions (Lynch & Vaandrager, *Information and Computation*
121(2):214–233, 1995, §3). The converse direction — "T3 permits ⟹ T4 permits"
(behavioral completeness) — is actively **false**: `T3.Fix` accepts an arbitrary
piece on every call, admitting traces like "`Fix X` forever" for a fixed `X`, which
no reachable T4 state can produce once `bag_` is forced to biject with `Piece`
(`PieceSet`, `MaxBagLen = |Piece| ≥ 2`, §3 of `implementation.md`). This is a
property of the model, referenced here, not re-derived.

## 2. State mapping α

`α_T4(js) = { s3 := α_T3(js.s3); bagLen := js.bag_.length; bag := βbag(js.bag_);
next := βnext(js.next_) }` — apply `t3/proofs.md`'s `α_T3` to the embedded
machine. `bagLen`, `bag`, and `next` are the three fields of `Draw`; each is
derived from the corresponding JS array on its own terms, since a JS array
(finite, current length meaningful) and a Rocq `ℕ → Piece` function (total,
paired with a separate bound) aren't the same shape.

**`next`.** `next_` is a Rocq function `ℕ → Piece`, but only `[0, NextLen)` is
ever read (`next_d 0` by `DrawNextPiece`/`fₑ`; `ShiftNext`'s own range).
`js.next_` is a JS array always exactly `NextLen` long (§4-T4b: `initPieceAndDraw`
fixes the length once, and `drawOnce`'s `shift()`+`push()` is length-neutral, so
no later call changes it). Define
```
βnext(arr) := λ i, if i < NextLen then arr[i] else <arbitrary>
```
Values at `i ≥ NextLen` are never read by anything the JS realizes, so their
choice is immaterial to every equality this file states.

**`bagLen`.** `implementation.md` §3 already fixes this: `bagLen_` has no JS
field, `js.bag_.length` *is* `bagLen_`. So `α_T4`'s `bagLen` component is simply
`js.bag_.length`, not a derived approximation of it.

**`bag`.** This is the one genuine type mismatch. Rocq's `bag_` is a *total*
function on all of `ℕ`, of which only `[0, bagLen_)` is ever read — `PieceSet`
(`Bijective bag MaxBagLen`) only constrains it at `bagLen_ = MaxBagLen` (right
after `Init` or a reset); `DrawNextPiece` reads exactly one index,
`bag_ (bagLen_ - 1)`, per call; nothing reads past index `bagLen_ - 1`. `js.bag_`
is a JS array whose *current length is* `bagLen_` (mid-cycle, `bag_.length <
NUM_PIECES` is the common case — this is why `checkInvariants` cannot use
`isPieceSet(bag_)` directly, §6). Define
```
βbag(arr) := λ i, if i < arr.length then arr[i] else <arbitrary>
```
so that `bag(i) = js.bag_[i]` exactly on `[0, bagLen)` and is unconstrained
outside it — the only range `T4.v` ever reads `bag` at, given `bagLen` tracks
the current bound.

**Why `Array.prototype.pop()` realizes `bag_ (bagLen_ - 1)`-indexed popping.**
`drawOnce`'s `bag_.pop()` (§4-T4a) removes and returns the array's *last*
element, i.e. index `bag_.length - 1` at the moment of the call — which, since
`bagLen = js.bag_.length` by the `bagLen` mapping above, is exactly index
`bagLen_ - 1`, the index `DrawNextPiece` reads (`bag_ d (bagLen_ d - 1)`).
Critically, `pop()` leaves every element at a lower index untouched, matching
Rocq's own non-reset branch (`bag_ := bag_ d`, the function itself is not
rewritten — only `bagLen_` decrements to "forget" the popped index): both sides
agree that `bag(i)` for `i < bagLen - 1` is unchanged by a non-resetting draw,
and `bagLen`'s own decrement (implicit in the JS via the shortened array,
explicit in Rocq via `bagLen_ - 1`) is what removes the popped index from the
readable range on both sides. On a resetting draw, `bag_.push(...bagNew)`
followed by `βbag` reproduces `bag_ := bagNew` exactly (`arr.length` is now
`bagNew.length = MaxBagLen`, so `βbag(arr)(i) = arr[i] = bagNew(i)` on the newly
full range `[0, MaxBagLen)`, the only range `bagNew` is constrained on by `H`).

## 3. `movePiece`/`rotatePiece` — full-use transfer

One-line delegations to `this.s3`; `bag_`/`next_` untouched (T4.v's
`MovePiece`/`RotatePiece` definitions). `t3/proofs.md`'s own action lemmas
transfer unchanged.

## 4. `fixPiece`/`fallStep` — full-use transfer with a supplied piece, plus a stuttering-step obligation

Two things to show, beyond what transfers from `t3/proofs.md`:

- **The piece supplied equals `next s 0` at the pre-state.** Definitional:
  `const p = this.next_[0]` (§4-T4d) reads index 0 before any mutation — this *is*
  the Rocq read `next_ d 0`, not a derived value requiring induction.
- **Guard failure implies zero mutation of `bag_`/`next_`.** True by construction of
  the peek-then-commit ordering: `this.drawNextPiece(bagNew)` (the only statement
  that mutates `bag_`/`next_`) is reached only after `fired` is confirmed `true`.
  This is not free — T4.v's `FixPiece` definition computes `d'`
  unconditionally via a `let` before the `option_map`, and a naive translation that
  mutates before checking `this.s3.fixPiece(p)`'s result would leave `bag_`/`next_`
  advanced even when the whole transition is rejected (concretely: calling
  `fallStep` when `gameover` is already `true` — `movePiece(-1,0)` fails on the
  `¬gameover` conjunct, `fixPiece` is attempted and *also* fails on the same
  conjunct, since nothing about `T3.FixPiece`'s guard is established merely by
  `T4.fixPiece` having been called). Rocq's `d'` being unconditionally *computed* is
  a pure-value binding with no observable effect once discarded by `option_map`
  over `None` — it does not license a stateful translation to commit an equivalent
  mutation on the rejected path. The peek-then-commit ordering in `model.js` avoids
  this: guard fails ⟹ `α` of the post-call state equals `α` of the pre-call state,
  the same stuttering-step property `t1/proofs.md`–`t3/proofs.md` rely on, now
  extended to T4's own new fields.

## 5. `holdPiece` — full-use transfer, plus two imported dependencies

Two things to state explicitly, not re-derive:

- **The `hold !== null` (skip) branch matches `T3.HoldPiece`'s own branch on the
  same underlying field**, independent of any invariant: `T4.v`'s `hold` is a
  direct passthrough of T3's own field (T4.v's `hold` field definition: `hold s
  := T3.hold (s3 s)`), so whichever branch `T4.holdPiece` takes, `T3.HoldPiece`'s internal `match
  hold s with Some p => p | None => p_new end` takes the corresponding one.
- **The `hold === null` (commit) branch's mutation can never precede a subsequent
  rejection** — cite `t3/proofs.md`'s `SwappedImplyHoldSome` (`swapped ⟹ hold ≠
  None`) here as an imported lemma. Its contrapositive, `hold = None ⟹ ¬swapped`,
  combined with the local `¬gameover` check (T4.v's `HoldPiece` definition checks
  it before the draw), guarantees `T3.HoldPiece`'s guard (`¬gameover ∧ ¬swapped`) holds whenever
  the mutating branch is taken — unlike `fixPiece`, no peek-then-commit
  restructuring is needed here, because there is no reachable "mutate then reject"
  state for `holdPiece` to begin with.

## 6. `TypeOK`/`BagNonEmpty`/`BagNextConsistent` — new to T4, and why they resist a
direct runtime check

These have no T3 analogue and need their own induction over `drawOnce`'s two
branches (reset / no-reset), checked against `BagNextConsistent`'s `k = min(MaxBagLen
- bagLen, NextLen)` formula in each case — not carried out in this file; it is
`proofs.md`'s own obligation to discharge. `TypeOK` preservation across a reset
additionally needs `H`'s `PieceSet bagNew` — `assertPieceSet` (a runtime check)
stands in for a Rocq proof term here; the obligation is *conditional on the check
having passed*, not unconditional.

A representational subtlety, worth stating explicitly rather than leaving implicit
in code comments: `TypeOK(s) := PieceSet(bag s)` is a statement about the
*unbounded* Rocq function `bag_`, bijective on `[0, MaxBagLen)` **regardless of
`bagLen_`'s current value** — in the non-reset branch, `bag_ d' = bag_ d` (the
function itself is untouched; only `bagLen_` decrements to "forget" the popped
index). The array representation has no such luxury: `this.bag_.pop()` genuinely
removes the element, so the JS array's *current* length is `bagLen_`, not
`MaxBagLen`, almost always (only immediately after a reset does `bag_.length ===
NUM_PIECES` hold). Consequently `isPieceSet(bag_)` — correct for validating a
*candidate* `bagNew` (`H`) — is **not** the right check for `TypeOK(s)` on the live
`bag_`: it requires full length on every call and would fail on every
non-freshly-reset state. The array-checkable analogue of `TypeOK` is weaker —
`bag_` is always a *prefix* of some valid piece set: non-empty (`BagNonEmpty`,
checked separately), no longer than `NUM_PIECES`, elements pairwise distinct,
elements drawn from `Piece`. This is what `model.js`'s `checkInvariants` asserts;
it is sound (a subset of a permutation is automatically distinct) but strictly
weaker than `TypeOK` itself, which — like `BagNextConsistent` — is not fully
checkable against the finite-array
representation and remains a `proofs.md`-only obligation beyond this weaker check.

## 7. `Init`

`InitRefineT3` (T4.v's `InitRefineT3` proof) needs `unfold Init, InitPiece,
InitPieceAndDraw; destruct (BuildInitNext ...)` to force both call sites' pair
destructuring to the same term before `reflexivity` applies. The JS-side analogue:
`initPieceAndDraw` is called exactly once in the constructor and its `p` is what
seeds `T3Eng.Machine` — there is no JS equivalent of the definitional-unfolding
friction. The JS translation is *simpler* to reason about here than the Rocq
original, not harder.

## 8. Cap soundness — not applicable

T4 introduces no new arithmetic on `score`/`combo`/`totalClearedLines`.

## 9. Each action — summary

- **`movePiece(dy,dx)`/`rotatePiece(cw)`** — one-line delegation, full use (§3).
- **`fixPiece(bagNew)`** — full use with a supplied piece; peek-then-commit ordering
  restores the stuttering-step property (§4).
- **`fallStep(bagNew)`** — disjoint-guard sequencing, unaffected by T4 (delegates to
  `movePiece`/`fixPiece`, both covered above).
- **`holdPiece(bagNew)`** — full use; two imported dependencies, no restructuring
  needed (§5).
