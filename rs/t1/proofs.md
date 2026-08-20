# proofs.md — refinement proof: `model.rs` ⊑ `T1.v`

Follows the `rocq-to-rust` skill's `proofs.md` skeleton (skill §6), in the order:
parameter mapping, state mapping α (§1–§2), helper lemmas (§3), each action (§4),
disjunctive actions (§5), the coupling invariant (§6), box-determinism (§7),
integer-range safety (§8), `Init` (§9), the non-`Next` "helpers for refining models"
definitions (§10), and the `check_axioms`/`Axiom` correspondence (§11).

> **Scope.** This proof transfers **safety/invariants** only. Liveness and fairness
> (e.g. "a fall eventually fixes") are out of scope and are not claimed (D11).

All section/definition references without a file prefix are to `T1.v`; `Dn`/`D-Name`
references are to `implementation.md`'s decision register (§1).

---

## 1. Parameter mapping

The proof is generic over any `P: Params` for which `check_axioms::<P>()` (§11)
succeeds. Such a `P` instantiates `T1.v`'s abstract parameters as follows:

| `T1.v` parameter | Rust source | Rocq value |
|---|---|---|
| `Piece` | `P::Piece` | `P::Piece` itself |
| `PW` | `P::PW` | `P::PW` (as `ℤ`) |
| `InitialMainGrid` | `P::initial_main_grid()` | `⟦P::initial_main_grid()⟧₍₀,₀₎` (§2) |
| `ForbiddenGrid` | `P::forbidden_grid()`, `P::FY`, `P::FX` | `⟦P::forbidden_grid()⟧₍FY,FX₎` |
| `RotGrid p r` (`r ∈ {0,1,2,3}`) | `P::rot_grid(p, r as u8)` | `⟦P::rot_grid(p, r as u8)⟧₍₀,₀₎` |
| `InitialYX p` | `(P::initial_y(p), P::initial_x(p))` | itself, as a pair |

`RotGrid`'s Rocq domain is `Piece → ℤ → Grid` (unconstrained for `r` outside `[0,4)`);
the mapping above is only defined — and only needs to be defined — for `r ∈ {0,1,2,3}`,
since `pr`/`pr2` never leave that range in any reachable Rust state (§6, §8) and no
Rust code ever calls `P::rot_grid` with any other `r`.

Every grid on the right is an **α-image** of a Rust array (§2's coercion `⟦_⟧`), so
every one of them is automatically `Contained` (D-Contained, §7) and has the box its
`.len()`/`.len()` of the first row report (§7) — these are representational facts about
`⟦_⟧`, not properties that need to be checked of the *instance* separately.

---

## 2. Bounded-structure coercion `⟦_⟧` and the state mapping α

### 2.1 `⟦_⟧`

For a 2-dimensional array `g: Vec<Vec<T>>` with `occ: T -> bool` (`occ(b) = b` for
`bool`, `occ(c) = c.is_some()` for `Option<Piece>`, D1) and an embedding origin
`(oy, ox): ℤ×ℤ`:

```
⟦g⟧₍oy,ox₎ = {| L  := λ y x, if oy ≤ y < oy+H ∧ ox ≤ x < ox+W then ⟦occ(g[(y-oy) as usize][(x-ox) as usize])⟧ else false
             ;  HW := (H, W)   where H := ⟦g.len() as ℤ⟧, W := ⟦if H>0 then g[0].len() else 0⟧
             ;  YX := (oy, ox)
             |}
```

Total and well-defined for every `g` (no partiality: the `if` covers every `(y,x):
ℤ×ℤ`, and the `then`-branch's index is in-bounds exactly when the guard holds). This is
D1's coercion, generalized with an explicit origin so it covers both the always-`(0,0)`
grids (`InitialMainGrid`, `mg`, every `RotGrid` image, D15) and `ForbiddenGrid`
(embedded at `(FY,FX)`, D15) uniformly.

**`⟦g⟧` is `Contained` by construction (D-Contained):** `Contained X ≡ ∀ y x,
OutsideBox X y x → L X y x = false`, and `⟦g⟧`'s own `L` is defined to be `false`
outside `⟦g⟧`'s box by the `if`'s `else` branch — this holds for *any* `g`, with no
hypothesis on `g`'s content. No runtime check is ever needed for a `Contained` conjunct
applied to an α-image (§11).

### 2.2 State mapping α

```
α(rs) = {| mg          := ⟦rs.mg⟧₍₀,₀₎
        ;  p            := rs.p
        ;  pyx           := (rs.py, rs.px)
        ;  pr            := rs.pr as ℤ
        ;  gameover      := rs.gameover
        ;  clearedLines := rs.cleared_lines as ℕ
        |}
```

**Totality and well-definedness.** `⟦_⟧` is total (§2.1). `rs.pr as ℤ` is total (`u8 →
ℤ` never fails). `rs.cleared_lines as ℕ` requires `rs.cleared_lines ≥ 0`: true by
construction — `cleared_lines` is initialized to `0` (`Machine::new`) and every other
write is `self.mg.iter().filter(...).count() as i64` (`fix_piece`), a `usize → i64`
cast of a `count()`, which is non-negative. So α is total on every `Machine<P>` value a
well-typed program can construct, not merely on reachable ones.

**Homomorphism condition 1 (α sends initial states to initial states)** is §9's `Init`
correspondence. **Condition 2** (the commuting-square diagram) is discharged
action-by-action in §4, using the coupling invariant of §6.

---

## 3. Helper lemmas

One lemma per non-trivial free function in `model.rs`. Every lemma below implicitly
assumes its Rust-array argument(s) are α-images (§2.1) — the only shape `model.rs` ever
passes to them — so `Contained`/box facts about the Rocq side are always available via
D-Contained without restating it per lemma.

### L-dims
For `g: Vec<Vec<T>>`, `dims(g) = (H, W)` computed as `(g.len(), g[0].len())` (with the
`H=0` short-circuit, D12) equals `(H ⟦g⟧, W ⟦g⟧)`. *Proof:* immediate from `⟦_⟧`'s own
`HW` field, which is defined as exactly that pair. `g[0].len()` panics only when
`g.len()=0`, ruled out at every call site by `type_ok` (§6: `HM > 0`, `AxiomsInitialMainGrid`).

### L-intersect
`intersect(g1,y1,x1,g2,y2,x2) = true ⟺ ⟦g1⟧₍y1,x1₎ ∩ ⟦g2⟧₍y2,x2₎ ⊈ ∅`.

*Proof.* Unfold the right side: `X ⊆ ∅` (`GridInclude X EmptyGrid`) quantifies only over
`X`'s own declared box (`seqz (Y X) (H X)` × `seqz (X X) (W X)` — `EmptyGrid`'s box is
`0×0`, so the `implb`'s consequent is vacuously `false`, reducing `X ⊆ ∅` to `∀(y,x) ∈
X`'s box: `L X y x = false`). With `X := g1 ∩ g2` (`GridIntersect`), `X`'s box is the
max/min-formula overlap of `g1`'s and `g2`'s boxes, and `L X y x = L g1 y x ∧ L g2 y x`.
So `X ⊈ ∅ ⟺ ∃(y,x)` in that overlap with both `L`s true.

`intersect`'s loop scans `g1`'s own array (`g1`'s box, by `⟦_⟧`), and for each occupied
cell (`c1.occ()`), computes the absolute coordinate and — after the guard-before-index
check (D9) — tests occupancy in `g2`. Any `(y,x)` the loop finds satisfying both tests
lies in `g1`'s box (the loop only ever visits there) and, by the guard, in `g2`'s box —
i.e. in the overlap, matching the Rocq quantifier's domain exactly. Conversely any
`(y,x)` in the overlap with `L g1 y x ∧ L g2 y x = true` is visited by the loop (every
cell of `g1`'s box is visited) and passes both tests. Equality of the two existentials
follows. ∎

### L-occupied_inside
`occupied_inside(g1,y1,x1,g2,y2,x2) = true ⟺ ⟦g1⟧₍y1,x1₎ ⊆ Full ⟦g2⟧₍y2,x2₎`.

*Proof.* `Full g2`'s box is `g2`'s own box, but its `L` is the *unconditional* constant
`true` (`Constant g2 true`, ignoring `g2`'s own box entirely). Substituting into
`GridInclude`'s definition: `implb (L g1 y x) (inbox(g2,y,x) ∧ true) = implb (L g1 y x)
(inbox(g2,y,x))` — i.e. "every occupied cell of `g1` lies in `g2`'s box", independent of
`g2`'s content, quantified over `g1`'s own box (as in L-intersect). `occupied_inside`'s
loop visits exactly `g1`'s occupied cells and returns `false` the first time one falls
outside `g2`'s bounds (`ay < y2 ∨ ay ≥ y2+h2 ∨ …`), `true` otherwise — a direct
transcription of that universally-quantified implication. ∎

### L-fully_contained_in
`fully_contained_in(g1,y1,x1,g2,y2,x2) = true ⟺ ⟦g1⟧₍y1,x1₎ ⊆ ⟦g2⟧₍y2,x2₎` (bare
`GridInclude`, no `Full`). *Proof.* Same quantifier-domain argument as L-intersect
(restricted to `g1`'s box); the consequent is now `inbox(g2,y,x) ∧ L g2 y x` verbatim
(no `Full` to simplify away), matching `fully_contained_in`'s bounds-guard-then-content
check exactly. ∎

### L-bbox_inside_bbox
`bbox_inside_bbox(g1,y1,x1,g2,y2,x2) = true ⟺ Full ⟦g1⟧₍y1,x1₎ ⊆ Full ⟦g2⟧₍y2,x2₎`.
*Proof.* Both sides are `Full`, so by the L-occupied_inside argument the consequent
degenerates to a pure box-containment test with *both* operands' content irrelevant;
unfolding further, `Full g1 ⊆ Full g2 ⟺ g1`'s box ⊆ `g2`'s box as rectangles (every
`(y,x)` in `g1`'s box is, vacuously since `L(Full g1) y x=true` always, required to be
in `g2`'s box) `⟺ y1 ≥ y2 ∧ y1+h1 ≤ y2+h2 ∧ x1 ≥ x2 ∧ x1+w1 ≤ x2+w2` — exactly
`bbox_inside_bbox`'s four-conjunct return expression. ∎

### L-is_full_row
For a row `r` at absolute `y`, embedded grid `g` with box `[Y,Y+H)×[X,X+W)`, and `Y ≤ y
< Y+H`: `is_full_row(r, occ) = true ⟺ IsFullLine ⟦g⟧ y` (equivalently `IsFullLineb ⟦g⟧ y
= true`, since `y` is in-box so the `implb`'s antecedent holds). *Proof.* `IsFullLine g
y ≡ ∀x ∈ [X,X+W): L g y x = true`; `is_full_row`'s `row.iter().all(occ)` is exactly this
quantifier specialized to the row array, whose indices `0..W` correspond 1-1 to
`x ∈ [X,X+W)` under `⟦_⟧`. ∎ (Every call site in `fix_piece` calls it on a row of `mg`
at an in-box `y`, so the "`y` in box" hypothesis always holds — see §4.3.)

### L-valid
`valid::<P>(g, p, py, px, pr) = true ⟺ Valid ⟦g⟧₍₀,₀₎ p (py,px) (pr as ℤ) = true`, for
`0 ≤ pr < 4` (established by §6). *Proof.* `Valid g p pyx pr ≡ let gp := RotGrid p pr ⊕
pyx in (gp ⊆ Full g) ∧ (gp ∩ g ⊆ ∅)`. `RotGrid p pr ⊕ pyx` (`GridTranslate`, embedding
`RotGrid p pr`'s own `(0,0)`-origin box at `pyx`) is exactly `⟦P::rot_grid(p, pr as
u8)⟧₍py,px₎` by §1's parameter mapping and the translate-then-embed identity `⟦g⟧₍₀,₀₎ ⊕
(dy,dx) = ⟦g⟧₍dy,dx₎` (immediate from `⟦_⟧`'s definition — translating shifts both the
box origin and the domain the content function reads at, which is exactly what
re-embedding at a different origin does). Substituting: `valid`'s two conjuncts are
L-occupied_inside and (negated) L-intersect applied to `pg := P::rot_grid(p,pr)`
embedded at `(py,px)` against `g` embedded at `(0,0)` — precisely `valid`'s two calls,
`&&`-combined exactly as `Valid`'s two conjuncts are `&&`-combined. ∎

### L-can_move_piece
`can_move_piece::<P>(dy, dx, s) = true ⟺ CanMovePiece (dy,dx) α(s) = true`. *Proof.*
`CanMovePiece`'s three-way direction disjunction is transcribed verbatim (identical
`&&`/`||` structure); its `Valid (mg s) (p s) pyx2 (pr s)` conjunct is L-valid applied to
`α(s).mg = ⟦s.mg⟧`, `α(s).p = s.p`, `pyx2 = (s.py+dy, s.px+dx)` (matching `can_move_piece`'s
`py2,px2`), `α(s).pr = s.pr as ℤ` — all four arguments agree by α's definition (§2.2). ∎

### L-rem_euclid
`(a: i64).rem_euclid(4) = (a mod 4 : ℤ)` for every `a` that arises (`s.pr as i64 +
{-1,1}`, i.e. `a ∈ {-1, 0, 1, 2, 3, 4}` given `s.pr ∈ {0,1,2,3}` — §6). Table:

| `a` | `a.rem_euclid(4)` | Rocq `a mod 4` |
|---|---|---|
| -1 | 3 | 3 |
| 0 | 0 | 0 |
| 1 | 1 | 1 |
| 2 | 2 | 2 |
| 3 | 3 | 3 |
| 4 | 0 | 0 |

`i64::rem_euclid`'s contract (always non-negative for a positive divisor) and Rocq's
`mod` (mathematical, always non-negative) agree on every input, not just this table —
the table only enumerates the inputs `rotate_piece` can actually produce (D4).

### No lemma needed: `occ`
`occ`/`Cell::occ` is not a separate Rocq definition to match against — it *is* `⟦_⟧`'s
`if`-branch content read, stated once in §2.1's definition of `⟦_⟧` rather than as an
independent correspondence.

### L-can_rotate_piece
`can_rotate_piece::<P>(cw, s) = true ⟺ ¬gameover s ∧ RotatePiece cw α(s) ≠ None`, i.e.
`can_rotate_piece`'s postcondition is exactly "a plain rotation would fire," *given*
`¬gameover s` (`can_rotate_piece` does not itself read `s.gameover` — same omission
`can_move_piece` makes, §3's own precedent — so the equivalence is stated relative to a
`¬gameover` hypothesis supplied by the caller, not derived here). *Proof.* Let `pr2 :=
(s.pr as i64 + (if cw then -1 else 1)).rem_euclid(4) as u8`. By L-rem_euclid, `pr2 as ℤ =
(pr s + (if cw then -1 else 1)) mod 4` — exactly `RotatePiece`'s own `pr2` binding.
`can_rotate_piece`'s body is `valid::<P>(&s.mg, s.p, s.py, s.px, pr2)`; by L-valid this is
`Valid ⟦s.mg⟧ (s.p) (s.py,s.px) (pr2 as ℤ) = Valid (mg α(s)) (p α(s)) (pyx α(s)) pr2` —
exactly `RotatePiece cw`'s own guard conjunct (`§4.2` below shows `rotate_piece`'s guard,
minus `gameover`, is this same `Valid` call). `RotatePiece cw s = Some s'` iff `¬gameover
s ∧ Valid (mg s) (p s) (pyx s) pr2`; under the hypothesis `¬gameover s`, this reduces to
exactly `can_rotate_piece`'s value. ∎ No caller of `can_rotate_piece` in this codebase
relies on the `gameover`-unconditional direction of this lemma — `t6::model`'s
`rotate_kick_piece` checks `s1.gameover` itself, immediately adjacent to the call
(`implementation.md` §0.2, §4-T6b), the same division of labor `fix_piece`'s `self.gameover
|| can_move_piece(-1,0,self)` guard already uses for `can_move_piece`.

---

## 4. Each action

Every lemma below assumes `type_ok(s)` (§6) as a hypothesis, discharged once
inductively in §6, not re-argued per action (skill §6.3).

### 4.1 `move_piece(&mut self, dy, dx) -> bool` ≙ `MovePiece (dy,dx)`

**Guard.** Rust: `self.gameover ∨ ¬can_move_piece(dy,dx,self)` → `false`. Rocq: guard to
proceed is `¬gameover s ∧ CanMovePiece (dy,dx) s`. By De Morgan and L-can_move_piece,
the Rust early-return condition is exactly the negation of the Rocq guard: `return
false` fires iff `MovePiece` would return `None` (a stuttering step, licensed by
`Next`'s `Stutter` arm — no field is touched, so `α` of the unchanged Rust state equals
the Rocq pre-state, satisfying the "guard fails → stutter" case, skill §6.3).

**Success.** `self.py += dy; self.px += dx;` — reads `self.py`/`self.px` (pre-state)
before writing, so no ordering hazard (skill §4b). Compare to Rocq's `pyx := (py s+dy,
px s+dx)`, all other fields unchanged: `α`'s `pyx` field becomes `(s.py+dy, s.px+dx) =
(py s + dy, px s + dx)`, matching; `α`'s `mg`/`p`/`pr`/`gameover`/`clearedLines` fields
are unchanged Rust-side and the Rocq definition explicitly carries them unchanged too
(`mg := mg s; p := p s; pr := pr s; gameover := gameover s; clearedLines := clearedLines s`).
`α` commutes with the step. ∎

### 4.2 `rotate_piece(&mut self, cw) -> bool` ≙ `RotatePiece cw`

`pr2 := (self.pr as i64 + delta).rem_euclid(4) as u8`, `delta = if cw {-1} else {1}`.
By L-rem_euclid, `pr2 as ℤ = (pr s + (if cw then -1 else 1)) mod 4` — exactly Rocq's
`pr2`. **Guard**: `self.gameover ∨ ¬valid::<P>(&self.mg, self.p, self.py, self.px,
pr2)` → `false`; by L-valid and De Morgan this is the negation of `¬gameover s ∧ Valid
(mg s) (p s) (pyx s) pr2`, so guard-fails and guard-holds correspond exactly as in §4.1.
**Success**: only `self.pr = pr2` is written; `α`'s `pr` field becomes `pr2 as ℤ`,
matching Rocq's `pr := pr2` with every other field explicitly unchanged on both sides. ∎

### 4.3 `fix_piece(&mut self, p_new) -> bool` ≙ `FixPiece p_new`

**Guard.** `self.gameover ∨ can_move_piece(-1,0,self)` → `false`, i.e. proceeds iff
`¬self.gameover ∧ ¬can_move_piece(-1,0,self)`; by L-can_move_piece this is exactly
Rocq's `¬gameover s ∧ ¬CanMovePiece (-1,0) s`. (Written via the `can_move_piece` call
rather than a reduced `¬valid(…)` form, for textual fidelity to `T1.v`'s own guard —
implementation.md §6.)

**`u` — `overlay_piece` implements `(mg s ∪ (PieceGrid s ⊕ pyx s)) ∩ Full (mg s)`, in
place.** Let `pg := ⟦P::rot_grid(s.p, s.pr)⟧₍s.py,s.px₎` (= `PieceGrid α(s) ⊕ pyx α(s)`,
by the translate-then-embed identity of L-valid). `GridUnion (mg s) pg` has box
`[min(0,s.py), max(HM, s.py+PW)) × [min(0,s.px), max(WM, s.px+PW))` (Rocq's min/max
formula) — a box that always *contains* `mg s`'s own box `[0,HM)×[0,WM)`, since
`min(0,·) ≤ 0` and `max(HM,·) ≥ HM` unconditionally. Intersecting with `Full (mg s)`
(same box as `mg s`, unconditionally-true content) clips the result's *box* down to
exactly `mg s`'s box (`max(0, min(0,s.py)) = 0`, and symmetrically for the other three
bounds — standard interval-intersection algebra applied to a box already known to
contain the other), while its *content* at any `(y,x)` inside that box is `(L(mg s) y x
∨ L pg y x) ∧ true = L(mg s) y x ∨ L pg y x` — unclamped, since `Full`'s content is
unconditionally `true` even outside its own nominal box, so intersecting never falsifies
a cell that was true. Call this `u`; `u`'s box is exactly `mg s`'s box, `L u y x = L(mg
s) y x ∨ L pg y x` throughout it.

`overlay_piece` writes `self.mg[gy][gx] = Some(piece)` for every occupied cell `(dy,dx)`
of `P::rot_grid(s.p,s.pr)`, at absolute `(gy,gx) = (s.py+dy, s.px+dx)`, **guarded** to
skip any `(gy,gx)` outside `self.mg`'s own array bounds (D9). Every cell it writes lies
in `self.mg`'s box, so after the loop `⟦self.mg⟧₍₀,₀₎`'s content at any `(y,x)` in that
box is: `Some` (occupied) if either the pre-overlay cell was occupied *or* the loop
wrote it there (`pg`'s translated cell at `(y,x)` was occupied) — i.e. `L(mg s) y x ∨ L
pg y x`, matching `u`'s content exactly. Cells of `pg` landing outside `self.mg`'s box
are dropped by the guard, which is correct: those coordinates are outside `u`'s own box
too (shown above), so `u`'s value there is irrelevant to any later read (§7's
box-determinism). This is the **extensional** equivalence lemma D13/skill §3.2 require
for `GridUnion`'s in-place fusion, stated as non-structural per skill §4f: it is proved
by comparing final content over `u`'s declared box, not by any step-by-step
correspondence with `GridUnion`'s own recursive/pointwise construction.

**`FullLineCount u` — the `cleared_lines` assignment.** `FullLineCount g =
FullLineCountImpl g (H g) (Y g)`, counting `y ∈ [Y g, Y g + H g)` with `IsFullLineb g y`.
Since `u`'s box is `[0,HM)×[0,WM)` (shown above), this is exactly `self.mg`'s row
indices `0..self.mg.len()`. `self.cleared_lines = self.mg.iter().filter(|row|
is_full_row(row, Option::is_some)).count() as i64` — by L-is_full_row, each row's test
matches `IsFullLineb u y` for that row's `y`, and the count matches
`FullLineCountImpl`'s count over the identical index range. This is `u = clearedLines`'s
Rocq value; the Rust computation runs on `self.mg` **after** `overlay_piece` (which is
exactly `u`, per the previous paragraph) and **before** the swap-partition below, so it
reads `u`, not `mg s` or the post-clear grid — matching `FullLineCount u`'s argument.

**`ClearFullLines u` — the swap-partition.** `ClearFullLines g = Resize (FilterFullLines
g (H g) (Y g) (Y g)) (H g) (λ_, false)`. `FilterFullLines` sweeps `y` from `Y g` (`=0`,
the *bottom* row under D3) upward, dropping full rows and writing each kept row into the
next available low index (`i`, starting at `0`) — i.e. kept rows are compacted toward
index `0` (the bottom), preserving their relative bottom-to-top visiting order; `Resize`
then pads the result back to height `H g` by adding rows filled `false` **above** the
existing top (`y ≥ Y g2 + H g2`, the larger-`y`/upper end under D3). This is standard
Tetris line-clear behavior: rows above a cleared line drop down, new empty rows appear
at the top.

`fix_piece`'s swap-partition scans `read = 0..self.mg.len()` (bottom to top, D3), swaps
each non-full row into the next `write` slot (`0, 1, 2, …`, i.e. compacted toward the
bottom, in encountered — bottom-to-top — order, `Vec::swap` moving only the row's
`Vec`-header, never cell contents), then fills `self.mg[write..]` (the remaining
*top* indices) with `None` (`row.fill(None)`, reusing the existing buffer rather than
allocating a fresh blank row). This is the same compaction (kept rows preserve relative
order, packed toward the bottom) and the same padding (new empty rows at the top) as
`FilterFullLines`+`Resize`, so `⟦self.mg⟧₍₀,₀₎` after the swap-partition equals
`ClearFullLines u`. This is the second **extensional**, non-structural equivalence
lemma D2/skill §3.2/§4f require, with the required **ordering clause**: the swap
preserves kept rows' relative bottom-to-top order, which is what makes the compaction
match `FilterFullLines`'s recursive left-to-right (`y, y+1, y+2, …`) sweep rather than
merely "some permutation with the same multiset of kept rows".

**Remaining fields.** `self.p = p_new; self.py = P::initial_y(p_new); self.px =
P::initial_x(p_new); self.pr = 0;` — reads only `p_new` (an argument, not a field), so
no ordering hazard; matches Rocq's `p := pNew; pyx := InitialYX pNew; pr := 0` via §1's
`InitialYX` mapping. `self.gameover = intersect(P::forbidden_grid(), P::FY, P::FX,
&self.mg, 0, 0)` — reads `self.mg` **after** the swap-partition (i.e. the post-clear
grid, `⟦self.mg⟧ = ClearFullLines u = mg2` in Rocq's naming) — by L-intersect, this
equals `ForbiddenGrid ⊈ ∅ (∩ mg2)`... precisely, `intersect(...) = true ⟺ ForbiddenGrid
∩ mg2 ⊈ ∅`, matching Rocq's `gameover := ForbiddenGrid ∩ mg2 ⊈ ∅` exactly (no negation
needed: `intersect`'s `true` reading *is* the `⊈∅` reading, per L-intersect's statement).

Every field-read in this method happens before that same field is overwritten
(`self.p`/`self.py`/`self.px`/`self.pr` are read by `overlay_piece` before being
reassigned to `p_new`'s values three lines later; `self.mg` is read by the `gameover`
computation only after the swap-partition has already produced its final value) — the
simultaneous-assignment argument (skill §4b) holds throughout. `α` commutes with the
step whenever the guard holds; guard-fails is a stutter as in §4.1. ∎

### 4.4 `fall_step` — see §5 (disjunctive action).

---

## 5. Disjunctive action: `fall_step(&mut self, p_new) -> bool` ≙ `FallStep p_new`

Rocq: `match MovePiece (-1,0) s with Some s' => Some s' | None => FixPiece pNew s end`.
Rust: `if self.move_piece(-1, 0) { return true; } self.fix_piece(p_new)`.

**Mutual exclusivity of the two guards, given `¬gameover s`.** `move_piece(-1,0)`'s
guard is `¬gameover ∧ can_move_piece(-1,0,·)`; `fix_piece`'s guard is `¬gameover ∧
¬can_move_piece(-1,0,·)`. These differ only in `can_move_piece(-1,0,·)` vs. its
negation, so whenever `¬gameover` holds, **exactly one** of the two guards holds — a
tautology, not an invariant that needs separate proof.

**Case `move_piece(-1,0)` succeeds.** Rust returns `true` immediately, having mutated
`self` exactly as §4.1 establishes; this matches Rocq's `Some s'` branch (`s' =
MovePiece (-1,0) s`), since `move_piece`'s guard holding is equivalent (§4.1) to
`MovePiece (-1,0) s` being `Some`, and its effect is `α`-equal to that `Some`'s payload.

**Case `move_piece(-1,0)` fails.** `move_piece`'s guard failing means **no field of
`self` is touched** (§4.1: the early return happens before any assignment) — so `self`
at the point `fix_piece(p_new)` is called is still the original pre-state `s`, not some
partially-mutated intermediate. Rocq's `None` branch evaluates `FixPiece pNew s` against
the *same* original `s` (not a mutated one — there is none, since Rocq has no mutation).
So the two computations start from the same state; `fix_piece`'s own correspondence
(§4.3) then applies verbatim, and — by the guard-mutual-exclusivity fact above,
`move_piece`'s guard failing (given `¬gameover`) implies `fix_piece`'s guard holds, so
this is not a "try both defensively" fallback but the direct sequencing the mutual
exclusion licenses (skill §6.4).

**Case `gameover`.** Both guards require `¬gameover`, so both `move_piece(-1,0)` and
`fix_piece(p_new)` return `false` without touching any field; `fall_step` returns
`false`, `self` unchanged. Matches Rocq: `MovePiece (-1,0) s = None` (guard fails) and
`FixPiece pNew s = None` (guard fails), so `FallStep pNew s = None` — a stuttering step,
licensed by `Next`'s `Stutter` arm exactly as in §4.1/§4.2's guard-fails case. ∎

---

## 6. Coupling invariant: `type_ok`

The state mapping α is a homomorphism only on well-formed Rust states; `type_ok`
(evaluated under `CHECK_INVARIANTS`, D7) is the representation invariant that makes it
one. Decomposes into (skill §6.5):

**(a) `type_ok` holds at `Machine::new` and is preserved by every method** (reachable
states are well-formed).

- *Base case (`Machine::new`).* `s.mg`'s dimensions are exactly `P::initial_main_grid()`'s
  (built row-for-row, cell-for-cell from it, §9); `s.pr = 0 < 4`; `s.p` is `Machine::new`'s
  own argument `p`, which every call site (§15.3, `random_piece`) draws from
  `P::piece_all()`. So all four `type_ok` conjuncts hold.
- *Inductive case.* `move_piece`/`rotate_piece` touch only `py`/`px`/`pr` — `pr`'s range
  (`< 4`) is preserved since `pr2` is always the result of `.rem_euclid(4) as u8` (§4.2),
  and neither `py`/`px` nor the untouched `mg`/`p` affect any `type_ok` conjunct.
  `fix_piece` (§4.3): the swap-partition only reorders/clears existing rows in place
  (`Vec::swap`, `row.fill(None)`) — never changes `self.mg.len()` or any row's `.len()`,
  so rectangularity is preserved; every written cell is `Some(piece)` where `piece` came
  from `P::rot_grid(...)`'s own table (§13.4's literals, all built from `Piece::all()`)
  or `None`, so the "every cell is `None` or a `piece_all()` member" conjunct holds;
  `self.pr = 0 < 4`; `self.p = p_new`, and `CHECK_INVARIANTS`'s own `debug_assert!` at
  the top of `fix_piece` already requires `p_new ∈ P::piece_all()` (D5). `fall_step`
  (§5) delegates entirely to `move_piece`/`fix_piece`, inheriting their preservation.

**(b) Under `type_ok`, every step meets the simulation condition** — this is exactly §4's
per-action work (§4.1–§4.3, §5), which is stated throughout under the hypothesis that
`type_ok(s)` holds of the pre-state (skill §6.3's blanket hypothesis) — none of those
arguments needed to *re-derive* rectangularity or range facts, only to use them (e.g.
L-dims relies on `type_ok`'s rectangularity to justify `g[0].len()` not panicking, §3).

`type_ok`'s pullback reading: `type_ok(s) ⟺ TypeOK (α(s))` for well-formed `s`.
`TypeOK s ≡ HW(mg s) = HW(InitialMainGrid) ∧ YX(mg s) = YX(InitialMainGrid) ∧ 0 ≤ pr s ≤
3`. The `HW` conjunct is exactly `type_ok`'s rectangularity-against-`initial_main_grid`
dimensions check (L-dims makes `HW ⟦self.mg⟧ = HW ⟦P::initial_main_grid()⟧`
definitionally, given matching `.len()`s). The `YX` conjunct (`= (0,0)`) holds for *any*
`⟦_⟧`-image embedded at `(0,0)` — a representational fact with no runtime check (D15,
§11), not something `type_ok` needs to assert. The `0 ≤ pr s ≤ 3` conjunct is
`type_ok`'s `s.pr < 4` (the `≥0` half is free: `pr: u8`, D-Rust — a type-level fact, not
a runtime check). `type_ok`'s remaining conjuncts (cell well-typedness) have no direct
`TypeOK` counterpart; they are the purely-representational half skill §6.5 describes —
the gap between Rocq's total `L` (well-typed by construction) and a finite `Vec<Vec<_>>`
(which needs rectangularity and cell-range asserted, since the type system alone allows
a ragged `Vec<Vec<_>>` even though it never permits an ill-typed *cell*, `Option<Piece>`
already ruling that out structurally). ∎

---

## 7. Box-determinism

Every bounded-structure field this proof reads (`mg`, `ForbiddenGrid`, `InitialMainGrid`,
every `RotGrid p r`) is a `⟦_⟧`-image, and `⟦_⟧` defines `L` to be `false`/absent outside
its own declared box unconditionally (§2.1) — so every such field is trivially
box-determined (its Rocq-side meaning is fully fixed by its in-box values, with nothing
observable depending on out-of-box cells, since out-of-box cells have no Rocq-side value
other than the fixed default `⟦_⟧` assigns them). This is what makes §2's `⟦_⟧`
coercion well-defined at all, and is relied on throughout §3–§4 without restating it —
in particular, `overlay_piece`'s decision to *drop* writes landing outside `self.mg`'s
array (§4.3) is sound only because those coordinates are provably outside `u`'s
box too, which is exactly a box-determinism argument. ∎

---

## 8. Integer-range safety

**Bound.** `B := max(HM, WM) + PW - 1`, where `HM, WM` are `P::initial_main_grid()`'s
dimensions (D10). `check_axioms` asserts `max(hm, wm) ≤ i64::MAX - P::PW + 1` (D10's
overflow-safe rearrangement of `B ≤ i64::MAX`) — vacuous for the shipped instance
(`B = max(22,10) + 4 - 1 = 25`, §13.6) but checked for every instantiation, not assumed.

**Every integer subterm stays in range.**

- `py, px` (piece position): bounded at spawn directly by `AxiomsInitialYX` (`1-PW ≤
  initial_y/x < HM/WM`). Inductively, `PieceOccupiedInsideBounds` (one of `Correct`'s
  conjuncts, transferred via §6's simulation argument together with L-valid/
  L-can_move_piece, since every position-changing action's guard is exactly `Valid`'s
  `⊆ Full mg` conjunct or a call that implies it) keeps every occupied cell of the piece
  inside `[0,HM)×[0,WM)` in every reachable state; since `AxiomsRotGrid` guarantees at
  least one occupied cell within the piece grid's own `[0,PW)×[0,PW)` box (no stronger
  placement guarantee is assumed for `r ≠ 0`), that cell alone already pins `py`/`px`
  within `(1-PW, HM)`/`(1-PW, WM)` — no tighter than, and consistent with, the spawn
  bound `AxiomsInitialYX` states directly. Both are within `±B`.
- `overlay_piece`'s `gy = self.py + dy`, `gx = self.px + dx` (`dy,dx ∈ [0,PW)`): bounded
  by the `py`/`px` bound above plus `PW`, comfortably under `B`'s own definition
  (`max(HM,WM)+PW-1` is exactly this sum's worst case).
- `pr`/`pr2` (`rotate_piece`, §4.2): `.rem_euclid(4)` result is always `∈ [0,4)`, cast to
  `u8`, never near any `i64`/`u8` boundary.
- `dy, dx` (`move_piece`'s arguments, `can_move_piece`'s direction check): always one of
  `{-1,0,1}` by construction (`Action::fire`, `main.rs`) — never a value that could
  interact with `B` at all.
- Loop bounds (`0..P::PW`, `0..self.mg.len()`, row indices): `P::PW` and `self.mg.len()`
  are themselves within `B` (the former by `check_axioms`'s `D10` assertion directly,
  the latter by §6's rectangularity invariant pinning it to `HM ≤ B`).

No subtraction/addition here can overflow `i64` given `B`'s headroom, and no cast can
wrap given the `py ≥ 1-PW`/`px ≥ 1-PW` bound together with the guard-before-cast
discipline (D9) — every `as usize` site is reached only after a `≥ 0` check specific to
that site (§3's guard-before-index lemmas all state this explicitly). ∎

---

## 9. `Machine::new(p, piece_source)` ≙ `Init p`

`gameover := intersect(P::forbidden_grid(), P::FY, P::FX, &mg, 0, 0)` — by L-intersect,
equals `ForbiddenGrid ∩ InitialMainGrid ⊈ ∅` (via §1's `InitialMainGrid` mapping and
`mg`'s construction below), matching Rocq's `gameover := (ForbiddenGrid ∩
InitialMainGrid) ⊈ ∅`.

`mg`'s construction (`P::initial_main_grid()`'s `false`/`true` cells become
`None`/`Some(piece_source())`) sets `⟦mg⟧`'s content at every `(y,x)` to
`occ(P::initial_main_grid()[y][x])`, which — since `occ` on a `bool` is the identity
(D1) — is exactly `P::initial_main_grid()[y][x]` itself, i.e. `⟦mg⟧ = ⟦P::initial_main_grid()⟧
= InitialMainGrid` (§1). *Which* piece a preset-occupied cell is tagged with is
irrelevant here: only `occ`/`is_some()` is ever read by any engine logic (§3's lemmas
all go through `occ`, never inspect *which* `Piece` occupies a cell), so `piece_source`'s
choices don't affect `⟦mg⟧`'s value, hence don't affect any Rocq-side observable.

`py := P::initial_y(p)`, `px := P::initial_x(p)`, `pr := 0`, `cleared_lines := 0` match
`Init p`'s `pyx := InitialYX p; pr := 0; clearedLines := 0` directly via §1's mapping.
`p := p` matches trivially. So `α(Machine::new(p, ·)) = Init p` for every `p`, and every
`p` a caller supplies is drawn from `P::piece_all()` (§15.3's `random_piece`), matching
Rocq's `∀ p : Piece, Init p` — every Rocq-side initial state has a corresponding
Rust-side one and vice versa. This is homomorphism condition 1 (§2.2). ∎

---

## 10. Helpers for refining models

`NewPieceState`/`NewPieceYXState`/`NewMainGridGameoverState` have no call site inside
`T1.v`'s own `Next`, nor anywhere in `model.rs`; they are still real `T1.v` `Definition`s
(the coverage check, implementation.md §10, requires them translated regardless). All
three are **total** in Rocq (no guard, no `option State`), so they are realized as
functions that mutate `s: &mut Machine<P>` in place and return `()`, rather than
returning a fresh state.

- **`new_piece_state::<P>(p_new, s)`** ≙ `NewPieceState p_new s`. Sets
  `s.p/py/px/pr := p_new, initial_y(p_new), initial_x(p_new), 0`, leaves
  `mg/gameover/cleared_lines` untouched — a direct field-for-field match against
  `NewPieceState`'s record update (`p := pNew; pyx := InitialYX pNew; pr := 0`, rest
  from `s`), via §1's `InitialYX` mapping. Total (no guard on either side): `α` commutes
  unconditionally.
- **`new_piece_yx_state::<P>(py_new, px_new, s)`** ≙ `NewPieceYXState (py_new,px_new)
  s`. Sets only `py/px`; matches `NewPieceYXState`'s `pyx := pyxNew`, rest unchanged,
  directly.
- **`new_main_grid_gameover_state::<P>(mg, gameover, s)`** ≙ `NewMainGridGameoverState
  ⟦mg⟧ gameover s` — for any `mg: Vec<Vec<Option<P::Piece>>>` (not necessarily one this
  proof has otherwise constrained), setting `s.mg := mg; s.gameover := gameover`,
  matching `NewMainGridGameoverState`'s `mg := mg; gameover := gameover`, rest
  unchanged, directly.

Each is a one-line field assignment on both sides with no guard and no field-ordering
hazard (nothing reads a field it also writes), so each is trivially total and
`α`-commuting. ∎

---

## 11. `check_axioms::<P>()` ↔ `T1.v`'s `Axiom` blocks

Every conjunct of every `Axiom` block is either asserted at runtime by `check_axioms`, or
explicitly discharged structurally (never silently dropped) — per skill §4h/§5.

| Axiom | conjunct | status |
|---|---|---|
| `AxiomsPW` | `PW > 0` | asserted (`P::PW > 0`) |
| `AxiomsInitialYX` | `1-PW ≤ InitialY p < HM`, sym. for `X`/`WM`, `∀p` | asserted, `∀ p ∈ P::piece_all()` |
| `AxiomsRotGrid` | `HW(RotGrid p r) = (PW,PW)`, `∀p,∀r∈[0,4)` | asserted (`g.len()`/row lens `== PW`) |
| `AxiomsRotGrid` | `YX(RotGrid p r) = (0,0)`, `∀p,∀r∈[0,4)` | **structural** — every `P::rot_grid` image is embedded at `(0,0)` by the API/convention itself (D15): no call site in `model.rs` ever attaches a non-zero origin to a `rot_grid` result before use; a non-`(0,0)`-origin piece grid is not a representable `Params::rot_grid` return value at all |
| `AxiomsRotGrid` | `Contained (RotGrid p r)` | **structural** (D-Contained, §2.1) |
| `AxiomsRotGrid` | `∃ occupied cell`, `∀p,∀r∈[0,4)` | asserted (`g.iter().flatten().any(is_some)`) |
| `AxiomsRotGrid` | `(RotGrid p 0 ⊕ InitialYX p) ⊆ ForbiddenGrid` | asserted (`fully_contained_in(g0, iy, ix, forbidden_grid, FY, FX)`, L-fully_contained_in) |
| `AxiomsInitialMainGrid` | `H>0 ∧ W>0` | asserted (`hm>0 ∧ wm>0`) |
| `AxiomsInitialMainGrid` | `YX = (0,0)` | **structural** (D15, same argument as `RotGrid`'s `YX` above) |
| `AxiomsInitialMainGrid` | `Contained` | **structural** (D-Contained) |
| `AxiomsInitialMainGrid` | `∀y, ¬IsFullLine y` | asserted (`!is_full_row(row,·)` per row, L-is_full_row) |
| `AxiomsForbiddenGrid` | `H>0 ∧ W>0` | asserted (`fh>0 ∧ fw>0`) |
| `AxiomsForbiddenGrid` | `Contained` | **structural** (D-Contained) |
| `AxiomsForbiddenGrid` | `Full ForbiddenGrid ⊆ Full InitialMainGrid` | asserted (`bbox_inside_bbox(forbidden_grid,FY,FX,initial_main_grid,0,0)`, L-bbox_inside_bbox) |

`D8`'s two conjuncts (`Piece` finite/fully-enumerated; the empty/sentinel-disjointness
implicit in `L`'s codomain) are discharged by the type system, not by any `Axiom` block
above — an exhaustively-`match`ed `#[derive]`d enum plus `Piece::all()`'s
`strum::EnumIter`-derived enumeration make finiteness a compile-time fact (skill §4h),
and `Option<Piece>`'s `None`/`Some` split makes "disjoint from empty" a compile-time
fact by construction (no other variant exists to confuse with either).

`D10`'s headroom assertion (`max(hm,wm) ≤ i64::MAX - PW + 1`) has no `T1.v` `Axiom`
counterpart — it is a translation-only proof obligation (§8), added here because it
must hold for the "Rust `i64` ≡ Rocq `ℤ`" assumption underlying every lemma above to be
sound, not because `T1.v` itself requires it. ∎

---

## 12. Coverage

Every `T1.v` `Definition`/`Fixpoint`/`Axiom`/`Record` name is accounted for above or in
`implementation.md`'s §3 naming map / §4 fusion rules: `Grid`/`L`/`HW`/`YX`/`H`/`W`/`Y`/`X`
(§2.1's `⟦_⟧`), `InBox`/`OutsideBox`/`Contained` (§7, D-Contained), `GridInclude`/`⊆`/`⊈`
(§3's four lemmas), `GridUnion`/`GridIntersect`/`GridTranslate` (§3's lemmas, §4.3's
fusion), `Full`/`Empty`/`EmptyGrid`/`Constant` (used inside §3's lemma statements, never
emitted standalone per implementation.md §3), `Piece`/`InitialMainGrid`/`ForbiddenGrid`/
`RotGrid`/`InitialYX`/`PW` (§1), `TypeOK` (§6), `Init` (§9), `Valid`/`CanMovePiece`
(§3), `MovePiece`/`RotatePiece`/`FixPiece`/`FallStep`/`Next` (§4–§5), `Resize`/
`IsFullLineb`/`FilterFullLines`/`ClearFullLines`/`FullLineCountImpl`/`FullLineCount`/
`PieceGrid` (§4.3's fusion), `Gameover`/`PieceOccupiedInsideBounds`/`PieceOnFreeBlocks`/
`HasFullLine`/`NoFullLine`/`CorrectWithoutGameover`/`Correct` (§6, mirrored by
`type_ok`/`check_invariants`), `NewPieceState`/`NewPieceYXState`/
`NewMainGridGameoverState` (§10), every `Axiom` block (§11). No `model.rs` behavior
relies on anything not accounted for above.
