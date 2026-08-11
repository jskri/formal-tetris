# proofs.md — refinement proof, `t5/model.js ⊨ T5.v`

Delta over `t4/proofs.md`. `T5.v` refines `T4.v` via `fₑ = id` and `fₛ = s4` — only
for `Event4` events (`T5.v`'s own comment: "The refinement holds only when
excluding Drop, i.e. it holds on T4 events."); `Drop` has no refinement claim, the same
shape as T3's exclusion of `Hold`.

## 1. Scope

Safety only. `Drop`'s exclusion is structural, stated by `T5.v` itself.

## 2. State mapping α

`α_T5(js) = { s4 := α_T4(js.s4); gy := js.gy }` — `gy` maps directly, no coercion.

## 3. `movePiece`/`rotatePiece`/`fixPiece`/`holdPiece` — full-use transfer, plus a `gy`-refresh obligation

Each is `option_map (UpdateShadowY s) (T4.<Action> ... (s4 s))` (`T5.v`'s
`MovePiece`/`RotatePiece`/`FixPiece`/`HoldPiece` definitions).
The new obligation, beyond what transfers from `t4/proofs.md`: **`gy` after a
successful call equals `shadowY` of the post-call state.** Definitional, not
inductive — `updateShadowY()` *is* that computation, called exactly when `T5.v`'s
`option_map` would reach `UpdateShadowY`. The stuttering-step property (guard fails
⟹ zero mutation) extends to `gy`: the failure path never calls `updateShadowY()`.

## 4. `shadowY`'s loop invariant

`shadowY(s1)` (`model.js`) uses **fuel**, not `py` itself, as its termination
measure — `fuel := py + PW - 1`, decremented alongside `py` on each continued
iteration. This is required, not a style choice: `py` can be negative down to
`-(PW-1)` (a piece anchored in a fixed `PW×PW` rotation grid can have its only
occupied cells near the top of that box, so the anchor can go negative while every
occupied cell stays inside the main grid — `AxiomsRotGrid`, `T1.v`), so a measure
bottoming out at `py = 0` would stop the search too early for such pieces/
rotations, disagreeing with where `T1.MovePiece`/`T1.FixPiece` (unbounded, `ℤ`-typed)
actually permit descending to.

Loop invariant, maintained at every iteration: `fuel = py_current + PW - 1`. Proof:
holds initially by construction; each continued iteration decrements both `py` and
`fuel` by 1, preserving the equality. Consequence: when `fuel` reaches 0,
`py_current = -(PW-1)` exactly. `AxiomsRotGrid` guarantees some occupied cell exists
at local row `≤ PW-1`, so `Valid(py)` is forced false once `py ≤ -PW` — meaning the
check the loop *would* perform one step further (`Valid(-(PW-1)-1) = Valid(-PW)`) is
guaranteed to fail regardless of which piece/rotation this is, so returning without
performing it is sound. Every check the loop *does* perform (down to and including
`Valid(-(PW-1))` itself, the last one before the fuel-exhausted return) is a real
`valid(...)` call, not assumed.

This loop invariant is what `t4-analogous` reasoning about `shadowY` needs as an
imported fact elsewhere in this file (§6) — proved here once, not re-derived per
call site.

## 5. `fallStep` — disjoint-guard sequencing (skill §6.6)

Unaffected by T5: delegates to `movePiece`/`fixPiece`, both covered by §3.

## 6. `dropPiece` — no-use for the relocation step, full use for the trailing fix

`T5.v`'s `DropPiece` has no guard of its own — it is the bare composition
`FixPiece bagNew H (NewPieceYXState (gy s, px s) s)`, unconditionally
relocating and then delegating entirely to `FixPiece`'s own rejection. `model.js`'s
`dropPiece` instead checks `this.gameover` *before* relocating anything. These
are sound realizations of the same definition, not two different things,
argued in two cases:

- **`¬gameover` at the pre-drop state.** `model.js` proceeds to relocate and
  call `fixPiece`. The bullets below show `fixPiece` is then *guaranteed* to
  fire — so `model.js`'s check changes nothing observable here; it's simply
  confirming a precondition the relocation needs anyway.
- **`gameover` at the pre-drop state.** `model.js` returns `false` immediately,
  touching nothing. `T5.v`'s own composition, run on this same state, would
  still construct `NewPieceYXState (gy s, px s) s` — but `NewPieceYXState`
  carries `gameover` through unchanged, so the relocated state is *also*
  `gameover`, and `FixPiece` on it forwards to `T4.FixPiece`, whose own guard
  (inherited to `T1.FixPiece`'s `¬gameover ∧ ¬canMovePiece(-1,0,·)`) rejects
  immediately, returning `None`. Rocq's composition is pure — constructing the
  relocated state and then discarding it on `FixPiece`'s rejection has no
  observable effect on `s` itself, since nothing was ever mutated in place, only
  substituted through. So `T5.v`'s own `DropPiece`, on a `gameover` state,
  already reduces to "`None`, `s` unaffected" — exactly what `model.js`'s
  upfront check produces directly, without constructing and discarding an
  intermediate relocated value. The upfront check is a JS-necessary
  optimization (imperative state needs the check *before* mutating, or the
  mutation would need undoing), not a divergence from a spec that has no
  guard to match: the two produce the same observable result on every input,
  by the reasoning above.

**Guard, revisited.** Given the above, both cases reduce to the same
per-field argument the rest of this section makes:
- **Soundness of the relocation, given `¬gameover` at the pre-drop state:**
  `LowestShadowY` (`T5.v`) states `gameover(s4 s) = false → gy s ≤ py(s4
  s) ∧ ValidPieceCannotGoDown s (gy s) ∧ ∀ y, y ≤ py(s4 s) → ValidPieceCannotGoDown
  s y → y ≤ gy s` — i.e. whenever `¬gameover` holds, `Valid(gy)` and `¬Valid(gy-1)`
  both hold for the current `px`/`pr`/`mg`. §3 shows `gy` always equals a fresh
  `shadowY` computation whenever the state was reached via a T5 action, and §4's
  loop invariant shows that computation itself satisfies `Valid(gy)`/`¬Valid(gy-1)`
  whenever the starting `Valid(py)` holds — supplied by `T4.Correct`'s
  `PieceOnFreeBlocks` whenever `¬gameover`. `T1.NewPieceYXState`'s relocation
  therefore preserves `PieceOccupiedInsideBounds`/`PieceOnFreeBlocks` at the
  relocated state (via `Valid(gy)`), and the relocated state's `py - 1` is exactly
  `gy - 1`, so `T1.FixPiece`'s guard (`¬gameover ∧ ¬Valid(py-1,...)`) is exactly
  `¬Valid(gy-1)` — already established. No case where the relocation is followed
  by a rejection exists; no peek-then-commit ordering is needed (contrast
  `t4/proofs.md` §4).
- **The trailing `fixPiece` call** is covered by §3 — its own `gy`-refresh
  obligation is inherited, not re-argued.

## 7. Cap soundness — not applicable

`dropPiece` introduces no new arithmetic and touches no capped accumulator; it only
relocates `py` and then delegates to `fixPiece`, already covered by `t2/proofs.md`
§5.

## 8. `Init`

`constructor(bagsFn)` ≙ `Init bags H` (`T5.v`): `this.s4 = new T4Eng.Machine(bagsFn)`
≙ `T4.Init bags H`; `this.gy = shadowY(...)` ≙ `ShadowY s4`, by definition.

## 9. Each action — summary

- **`movePiece`/`rotatePiece`/`fixPiece`/`holdPiece`** — full use, `gy`-refresh-on-
  success (§3), `shadowY`'s own correctness argued once (§4).
- **`fallStep`** — disjoint-guard sequencing (§5).
- **`dropPiece`** — no-use relocation + full-use fix, single upfront guard
  sufficient given `LowestShadowY` (§6).
