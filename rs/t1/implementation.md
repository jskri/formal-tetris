# implementation.md — ImplementationInstructions for T1 (Rust)

Per-model instructions for the transformation

```
FormalModel (T1.v)  ×  ImplementationInstructions (this file)
      ── rocq-to-rust skill ──▶  Code (model.rs, view.rs, main.rs, instance.rs)
                                  ×  Proofs (proofs.md)  ×  Tests (tests/)
```

This file is the **T1-Rust-specific source of truth**, applying the `rocq-to-rust` skill's
general rules to `T1.v`. Generated artifacts are never hand-edited: to change an artifact,
change this file or `T1.v` and regenerate. All references to `T1.v` are **by definition
name**, so renaming/reordering in the model is caught by the coverage check (§10), not
silently mismatched line numbers.

Every rule general to any Rocq→Rust translation is cited from the `rocq-to-rust` skill by
section number (`skill §N`), not restated here. Only T1-specific content — which grids
exist and their shapes, the naming map, guard bodies, the concrete instance data — is
stated directly, grounded in `T1.v`/`T1Proofs.v`. Decisions prefixed `D-Rust` name a
Rust-realization choice the skill leaves open, resolved here for T1.

## 0. Inputs, outputs, and what is frozen

Codegen-time inputs (this transformation):
- `T1.v` — the abstract model (parameters left abstract).
- this file.
- the `rocq-to-rust` skill.

Runtime input (NOT codegen-time, NOT derived from `T1.v`):
- `instance.rs` — the concrete instantiation of the abstract parameters, as a type
  implementing the `Params` trait (§2, §13).

Outputs: `model.rs`, `view.rs`, `main.rs`, `instance.rs`, `Cargo.toml`, `proofs.md`,
`tests/` (§9). A generation is **correct** iff `model.rs` refines `T1.v` (established by
`proofs.md`); the acceptance oracle (§10) is the operational check that provides evidence
for this, it is not itself the definition — regeneration determinism (§12) is what
governs equivalence between independent runs of the transformation.

## 1. Frozen decisions (decision register)

| id  | decision | rationale |
|-----|----------|-----------|
| D1  | Grids: `ForbiddenGrid` and every pure-boolean grid are `Vec<Vec<bool>>`, row-major, `g[y][x]`. `mg` and `RotGrid`'s output are `Vec<Vec<Option<Piece>>>` — `None` is the sole empty value, `Some(p)` the occupying piece. `occ` is the one predicate every cell-truth test in `model.rs` goes through: `occ(b: bool) -> bool { b }` for boolean grids, `occ(c: Option<Piece>) -> bool { c.is_some() }` for `mg`/`RotGrid`. | skill §2 (bounded structure → `k`-deep `Vec`, `k=2` for T1's grids; codomain-dependent `T`); `T1.v`'s abstract `Grid.L` is uniformly `bool` (occupancy only) — `mg`'s widening to `Option<Piece>` is an implementation-level addition for rendering, not part of the Rocq codomain, discharged as a trivial `occ`-agreement fact in `proofs.md` |
| D2  | `FilterFullLines` is **not** emitted — its recursion exploits `L`'s totality (writes a kept row at a compaction index that is only in the eventual box once the recursion unwinds), the pattern skill §4f rules out for structural translation. `ClearFullLines` is translated at the *observable* boundary only, fused into `Machine::fix_piece` (§6), always at the array's own index `0` (justified by D-invariant below, not assumed). | `T1.v`'s `FilterFullLines`; `Y g = 0` invariant, see D-reach; skill §4f, §3.2 |
| D-reach | Every grid `ClearFullLines`/`FullLineCount`/`IsFullLineb` is (conceptually) applied to at runtime — `self.mg`, and the overlay `FixPiece` builds before clearing — has Rocq origin `Y = X = 0`, by the `TypeOK`/`BoxUnionClamp`/`ClearFullLinesBox` argument. | `T1Proofs.v`: `BoxUnionClamp`, `ClearFullLinesBox` |
| D3  | Orientation: `y = 0` is the **bottom**; gravity decreases `y`. Renderer flips; engine does not. | `FallStep` |
| D4  | Rocq math `mod` → `a.rem_euclid(n)` (`i64::rem_euclid`), never `%`. Only site: `rotate_piece`. | skill §4a — Rust's `%` keeps the dividend's sign for negatives |
| D5  | Non-determinism is an **explicit method argument** (`fix_piece(p_new)`, `fall_step(p_new)`). No callback. | faithful to spec |
| D6  | First piece is a **constructor argument**: `Machine::new(p0, piece_source)`. | matches `Init p` |
| D7  | Invariant re-checks run under `CHECK_INVARIANTS` (module const, default `false`), independent of Rust's `debug_assert!`/build-profile mechanism. `type_ok` is the highest-value one. | skill §4c |
| D8  | `Piece` is a `Copy + Eq` enum with an exhaustive, derived enumeration (`Piece::all()`, §13.2); `rot_grid`/`initial_y`/`initial_x` pure. Finiteness and "disjoint from the empty sentinel" are **not** asserted in `check_axioms`: an exhaustively-matched enum and `Option<Piece>`'s `None`/`Some` split make both type-level facts instead of runtime axioms. | skill §4h |
| D9  | Guard-before-index everywhere; bounds conjuncts first, signedness checked before every `as usize` cast. | skill §4d, §4g; `proofs.md` fusion-idiom lemmas are stated against this exact conjunct order |
| D10 | Integer-range safety via bound `B := max(HM,WM)+PW−1`, where `HM`/`WM` are `H`/`W` of `InitialMainGrid`. Fields use `i64`. `check_axioms` asserts `B <= i64::MAX` — vacuous for the concrete instance (`B = 25`, §13.6) but stated for every instantiation, not assumed. | skill §6.7's bound-adoption rule, applied to `T1.v`'s own `InitialMainGrid`/`PW`; proven directly in `proofs.md` (§8) — not cited from an external bounds file |
| D11 | Only safety/invariants are claimed to transfer; no liveness. | skill §6, scope note |
| D12 | `W` is derived from `g[0].len()`; sound because `type_ok ⇒ H>0`. Do not special-case empty grids. | `AxiomsInitialMainGrid` gives `H>0`; skill §2 caveat |
| D13 | **Fusion is mandatory.** T1's grid algebra requires the four idioms of §4; skill §3.2/§4f additionally require in-place realization, not fresh allocation, wherever the result targets a uniquely-owned field (T1's `mg` — see §6). | `proofs.md` §2 (skill §6.2) |
| D14 | Position/offset data is always two scalars (`py,px` / `dy,dx` / `initial_y(p),initial_x(p)`), never a Rust tuple or struct, at every module boundary. | named struct fields force every construction site to write the field name (`Machine { py: e1, px: e2, .. }`), checked by the compiler; a positional tuple has no such check, so swapping two same-typed components compiles silently as a tuple but requires writing the wrong field name outright with named fields |
| D15 | `ForbiddenGrid` is the only instantiated grid with non-`(0,0)` Rocq origin. Represented as the array plus two separate `FY: i64`, `FX: i64` associated consts on `Params` — not tracked as `Machine` state — matching D1's array-only convention for grid *content*. | `AxiomsInitialMainGrid`'s `YX = (0,0)`; `AxiomsRotGrid`'s `YX gr = (0,0)`; skill §6.6's parameter-vs-state distinction |
| D16 | Fall period is `1.0s` (`FALL_PERIOD_SECS`, `main.rs`). A UI-pacing constant with no `Params`/`Machine` counterpart. | `T1.v`'s own design note: "time is intentionally not part of the model" |
| D17 | Input bindings (keyboard/gamepad) are fixed per §15.2's table, covering exactly `T1.v`'s five actions (move left/right/down, rotate cw/ccw) — no additional actions beyond `T1.v`'s own `Event` type. Move left/right/down bind to the physical arrow keys; rotate cw/ccw bind to whichever physical key currently produces the logical letters `x`/`z` under the system keyboard layout (D-Logical-Keys), not a fixed physical position. | §15.2 |
| D18 | `Params::Piece: 'static` (§2). Required for `piece_all`'s/`rot_grid`'s `&'static` return types to be well-formed at every generic `P: Params` call site, not just for concrete instantiations. | §2 |
| D-Contained | `Contained` holds automatically for the α-image of any grid array (`Vec<Vec<bool>>` or `Vec<Vec<Option<Piece>>>`, D1): the coercion `⟦g⟧` (`proofs.md` §2) *defines* `L` to be `false`/`None` outside `g`'s box. No runtime check is emitted for any `Contained` clause. | `proofs.md` §2 |
| D-Rust1 | `T1.v`'s abstract parameters (`Piece, InitialMainGrid, ForbiddenGrid, RotGrid, InitialYX, PW`) are realized as a `Params` trait (§2); `Machine<P: Params>` is generic over `P`. | skill §1 |
| D-Rust2 | `Machine<P>` and every grid it owns are passed to read-only callers (rendering, `check_invariants`, `type_ok`) by `&Machine<P>` / `&Vec<Vec<_>>`. No clone of `Machine` or of `mg` is ever taken outside `Machine`'s own methods. | skill §3.1 |
| D-Rust3 | `RotGrid`'s output is returned by `&'static` reference into a table built once, never a fresh allocation per call (§2, §13.4). | skill §3.1 — `RotGrid` is a pure function over a closed, finite domain; nothing ever mutates a returned grid |
| D-Window | The window opens fullscreen (`Conf { fullscreen: true, .. }`, §15.2/§15.4); `Esc` is the only way to quit, checked once per frame in the main loop before input processing. `platform` is left at macroquad's default — confirmed working fullscreen on Wayland as shipped. A UI/platform concern with no `Params`/`Machine` counterpart, same category as D16. | macroquad's `Conf`/`window_conf` mechanism (§15.1/§15.2); `miniquad::window::order_quit()` for the quit itself, reached through macroquad's re-export (`macroquad::miniquad`) — no extra `Cargo.toml` dependency |
| D-Logical-Keys | Cw/Ccw's key bindings (`x`/`z`, D17) are resolved to a physical `KeyCode` at runtime from the OS-translated character stream (`get_char_pressed`/`get_keys_pressed`), not hardcoded to a fixed `KeyCode`. Left/Right/Down stay on the physical arrow keys, unaffected by letter-layout differences. | macroquad's `KeyCode` enum reflects a fixed physical-key mapping, not the system keyboard layout, on at least some platforms/backends; `get_char_pressed`'s character stream is OS-translated on every platform macroquad targets |
| D-Grid-Centering | The grid is centered in the window on both axes: `cell_size` is the largest cell that fits the window's width and its margin-reduced height, and whichever axis has slack left over beyond that is centered via a per-frame `(origin_x, origin_y)` offset (§14.2/§14.3). A vertical-only margin (`VERTICAL_MARGIN_FRACTION = 0.05` of window height, reserved equally off the top and off the bottom) keeps the grid off the top/bottom edge; no horizontal counterpart was requested. | `view.rs`'s `Layout` struct |

## 2. File layout & module shape

```
t1/
  Cargo.toml
  src/
    lib.rs                # re-exports instance/model/view/misc (§9's tests/ link against this)
    instance.rs         # concrete Tetris parameters — a Params impl (§13)
    model.rs             # T1 engine (generated from T1.v)
    view.rs               # renderer (macroquad — a pure-Rust cross-platform 2D
                           # rendering/windowing/input crate, §14)
    misc.rs                # main.rs-only primitives reused by every crate's main.rs (§15)
    main.rs                # entry point (macroquad main loop) (§15)
  proofs.md
  tests/
    test_instance.rs     # test fixture (not the runtime instance.rs)
    model_unit_test.rs
    model_properties_test.rs
    model_fuzz_test.rs
    oracle.rs             # executable Rocq reference (see §9.4)
```

`lib.rs` exists only so `tests/*.rs` — each its own crate, per Rust's integration-test
convention — can reach `model`/`instance`/`view`/`misc` at all; `main.rs` alone isn't
linkable from `tests/` or from downstream crates. It is a single `pub mod instance; pub mod
misc; pub mod model; pub mod view;` and nothing else; `main.rs` consumes the lib crate
(`use t1::{instance, misc, model, view};`) rather than declaring the modules itself.

No `utils` module is emitted for `model`/`instance`/`view`. `bool`-grid construction from
raw dimensions has exactly one call site in the whole translation (`Machine::new`'s `mg`,
and even that is `Option<Piece>`, not `bool` — see D1's coercion note in §6) — the
single-call-site fusion principle already applied throughout this document (§3, §4, D13)
inlines it there rather than factoring out a module for it. `misc.rs` is a different kind
of module: not a grab-bag for grid algebra, but the `main.rs`-only constants/types/free
functions that `t2`'s (and later `t3`'s/`t4`'s) own `main.rs` reuse rather than
re-declare, since `main.rs` itself isn't linkable across crates (§15.6).

`model.rs` exports:

```rust
pub trait Params {
    type Piece: Copy + Eq + std::fmt::Debug + 'static;

    const PW: i64;
    const FY: i64;
    const FX: i64;

    fn piece_all() -> &'static [Self::Piece];
    fn initial_main_grid() -> &'static Vec<Vec<bool>>;
    fn forbidden_grid()    -> &'static Vec<Vec<bool>>;
    fn rot_grid(p: Self::Piece, r: u8) -> &'static Vec<Vec<Option<Self::Piece>>>;
    fn initial_y(p: Self::Piece) -> i64;
    fn initial_x(p: Self::Piece) -> i64;
}
```

`Piece: 'static` (D18): `piece_all`'s and `rot_grid`'s return types are `&'static
[Self::Piece]`/`&'static Vec<Vec<Option<Self::Piece>>>` — for a `&'static` reference into a
type to be well-formed, that type must itself satisfy `'static`, which for `Self::Piece`
requires the bound to be stated explicitly (an associated type has no implicit lifetime
bound). Every concrete `Piece` enum already satisfies this trivially (a plain enum with no
borrowed fields is `'static` automatically); the bound just makes that fact provable at
every generic `P: Params` call site, not only for concrete instantiations.

`rot_grid` returns a `&'static` reference into a table built once at startup (§13.4), never
a fresh allocation per call (D-Rust3, skill §3.1).

Order of translation follows `T1.v`'s `Parameter` order (`Piece, InitialMainGrid,
ForbiddenGrid, RotGrid, InitialYX, PW` → decomposed per D14/D15 into the trait items
above).

Parameter-independent grid algebra (§4's four idioms and their supporting predicates —
`occ`, `is_full_row`, `intersect`, `occupied_inside`, `fully_contained_in`,
`bbox_inside_bbox`) is emitted as **free functions**, generic only over a plain
`Copy + Eq` piece type where a grid carries `Option<Piece>`, not over `Params` — these
functions never call into `Params` (skill §1's free-function classification). Only the
functions/methods that call `Params::rot_grid`/`initial_y`/`initial_x` (`valid`,
`can_move_piece`, and every `Machine<P>` method) are generic over `P: Params`.
`GridUnion`, `ClearFullLines`, `FullLineCount`, `Resize`, and `PieceGrid` are **not**
emitted as free functions at all — each has exactly one call site in `T1.v` (inside
`FixPiece`), so each is fused into `Machine::fix_piece` per skill §3.2 rather than
factored out (§3, §4, §6).

`Machine<P: Params>`'s fields, constructor, and methods are as in §6. `type_ok`,
`check_invariants`, `check_axioms` as in §6/§7 — no free functions beyond §5, no
refactors, no helpers not listed here.

## 3. Naming map (Rocq → Rust), frozen

| Rocq | Rust |
|------|----|
| `Grid`, `L`, `HW`/`YX`, `H`/`W`/`Y`/`X` | not emitted as such; realized as `Vec<Vec<bool>>`/`Vec<Vec<Option<Piece>>>` (D1) plus, for `ForbiddenGrid` only, `Params::FY`/`Params::FX` (D15) |
| `InBox`, `OutsideBox`, `Contained` | not emitted (D-Contained; fusion §4) |
| `GridInclude` (`⊆`), bare | `fully_contained_in` : `bool` |
| `GridInclude` (`⊆`), as `_ ⊆ Full _` | `occupied_inside` |
| `GridInclude` (`⊆`), as `Full _ ⊆ Full _` | `bbox_inside_bbox` |
| `GridIntersect` (`∩`), as `_ ∩ _ ⊆/⊈ ∅` | `intersect` (negated at call sites) |
| `GridUnion` (`∪`) | not emitted; single call site, fused into `Machine::fix_piece` (§4 idiom 3, §6) |
| `GridTranslate` (`⊕`) | not emitted standalone; absorbed into offset arithmetic |
| `Full`, `Empty`/`EmptyGrid`, `Constant` | not emitted (D13) |
| `NewPieceGrid` | not emitted; its one use site is `fully_contained_in` |
| `IsFullLine` (Prop) | not emitted; `is_full_row(row, occ) -> bool` |
| `IsFullLineb` | not emitted as a standalone grid+index function; its row-level content survives as `is_full_row`, called directly on rows `Machine::fix_piece` already has in hand (§6) |
| `RotGrid` (parameter) | `Params::rot_grid(p, r)` |
| `Valid` | `valid(g, p, py, px, pr)` |
| `CanMovePiece` | `can_move_piece(dy, dx, s)` |
| `Resize` | not emitted; single call site (inside `ClearFullLines`), fused into `Machine::fix_piece` (§6) |
| `FilterFullLines` | not emitted; exploits `L`'s totality (D2), not structurally portable (skill §4f) |
| `ClearFullLines` | not emitted; fused into `Machine::fix_piece` (§6), per its *observable* definition (skill §4f) |
| `PieceGrid` | not emitted; single call site, inlined as `P::rot_grid(self.p, self.pr)` |
| `FullLineCount`/`FullLineCountImpl` | not emitted; fused into `Machine::fix_piece` (§6) |
| `NewPieceState` | `new_piece_state(p_new, s: &mut Machine<P>)` |
| `NewPieceYXState` | `new_piece_yx_state(py_new, px_new, s: &mut Machine<P>)` |
| `NewMainGridGameoverState` | `new_main_grid_gameover_state(mg, gameover, s: &mut Machine<P>)` |
| `Init` | `Machine::new` |
| `MovePiece` | `Machine::move_piece(&mut self, dy, dx)` |
| `RotatePiece` | `Machine::rotate_piece(&mut self, cw)` |
| `FixPiece` | `Machine::fix_piece(&mut self, p_new)` |
| `FallStep` | `Machine::fall_step(&mut self, p_new)` |
| `mg,p,py,px,pr,gameover,clearedLines` | `mg, p, py, px, pr, gameover, cleared_lines` (identical shape, D14) |
| `AxiomsPW`, `AxiomsInitialYX`, … | — (not emitted; checked by `check_axioms`) |

`NewPieceState`/`NewPieceYXState`/`NewMainGridGameoverState` have no call site inside
T1's own `Next`; `T1.v` defines them as reusable building blocks (`T1Proofs.v` proves
`Correct`/`CorrectWithoutGameover` for all three) that this document does not describe
further uses of. They are still real `T1.v` `Definition`s, so the coverage check (§10)
requires them to be translated regardless. Unlike `move_piece`/`rotate_piece`/`fix_piece`
(guarded, `option State` in Rocq), all three are total, so they're realized as functions
that mutate `s: &mut Machine<P>` in place and return nothing, rather than returning a
fresh state value — and, matching `T1.v`'s own file layout (its `(* Helpers for refining
models *)` section at the very end), placed in a trailing `model.rs` section of the same
name, after `check_invariants`, not inside `Machine`'s own `impl` block with the five
`Next`-reachable transitions.

## 4. Translation rules specific to T1

1. **`gp ⊆ Full g`** (location only): `occupied_inside(g1,y1,x1,g2,y2,x2)`.
2. **`gp ∩ g ⊆ ∅`**: `!intersect(g1,y1,x1,g2,y2,x2)`.
3. **`(g1 ∪ g2) ∩ Full g1`**: `T1.v` instantiates this idiom exactly once (`GridUnion` in
   `FixPiece`); per D13/skill §3.2, realized as an in-place overlay write onto `self.mg`
   inside `Machine::fix_piece` (§6), not as a standalone `union` function returning a
   fresh grid.
4. **bare `g1 ⊆ g2`**: `fully_contained_in(g1,y1,x1,g2,y2,x2)`.

`Full g1 ⊆ Full g2` (used once, `AxiomsForbiddenGrid`) is idiom (4) specialized to
`bbox_inside_bbox(g1,y1,x1,g2,y2,x2)`.

- **Offsets**: plain `i64` subtraction (no `rem_euclid` — D4's only site is rotation),
  then guard-before-index (D9): bounds conjuncts computed first, `g1[y as usize][x as
  usize]`/`g2[oy as usize][ox as usize]` read only once guarded, negativity ruled out
  before every `as usize` cast (skill §4g).
- **`Params::rot_grid(p, r)`**: opaque parameter of the model; thin pass-through, returns
  a `&'static` reference (§2), no allocation, no copy on any call.
- **`ClearFullLines`/`FullLineCount`** (D2, D-reach, idiom 3): realized together inside
  `Machine::fix_piece` (§6) as an overlay-then-swap-partition, per skill §3.2's worked
  T1 example — walk `self.mg`'s rows once, swap surviving rows into a compacted prefix
  (moving only `Vec`-header data, never cell contents), then reset the trailing rows'
  cells to `None` in place, recycling their existing buffers instead of allocating fresh
  blank rows. `is_full_row(row, occ)` is the one shared predicate both the cleared-line
  count and the partition test go through (D13's no-duplicated-logic requirement). The
  equivalence lemma this discharges is extensional, not structural (skill §4f) — it must
  additionally state that the swap-partition preserves kept rows' relative order.

## 5. Free functions — signatures (all pure; return `bool` unless noted)

```
occ                (c: Option<Piece>)                                  -> bool
fully_contained_in (g1, y1, x1, g2, y2, x2)                            -> bool
bbox_inside_bbox   (g1, y1, x1, g2, y2, x2)                            -> bool
is_full_row<T>       (row: &[T], occ: impl Fn(&T) -> bool)              -> bool
intersect          (g1, y1, x1, g2, y2, x2)                            -> bool
occupied_inside    (g1, y1, x1, g2, y2, x2)                            -> bool
valid<P: Params>   (g, p: P::Piece, py, px, pr)                        -> bool
can_move_piece<P>  (dy, dx, s: &Machine<P>)                            -> bool
new_piece_state<P>              (p_new, s: &mut Machine<P>)            -> ()
new_piece_yx_state<P>           (py_new, px_new, s: &mut Machine<P>)   -> ()
new_main_grid_gameover_state<P> (mg, gameover, s: &mut Machine<P>)     -> ()
```

`is_full_row` is generic over the cell type via an explicit `occ` argument, matching D1's
single-predicate discipline: bool grids call it with `occ = |&b| b`, `mg`'s rows (inside
`Machine::fix_piece`, §6) call it with `occ = Option::is_some`. `occ` takes `&T`, not `T`
— `Option::is_some` has signature `fn(&self) -> bool`, i.e. `fn(&Option<Piece>) -> bool`
as a function item, so `occ`'s signature must match that exactly for `Option::is_some` to
be usable as `occ` directly, with no wrapper closure. `T` needs no `Copy` bound, since
nothing is copied out of the row — `is_full_row`'s body is `row.iter().all(occ)`, `occ`
applied directly to the `&T` items `Iterator::all` already hands it.

The three `Helpers for refining models` functions (§3, §6) mutate `s` in place and return
`()` rather than a fresh state value — `T1.v`'s versions are total (no guard, unlike
`move_piece`/`rotate_piece`/`fix_piece`'s `option State`), so there's no failure case to
signal and no `MachineState`-shaped return value to construct.

`occupied_inside`/`intersect`/`fully_contained_in`/`bbox_inside_bbox` are generic over the
two grids' cell type only insofar as `occ` needs it (`bool` grids use identity,
`Option<Piece>` grids use `occ`); in practice this means two thin overloads or one
function generic over `T: Copy` with an `occ: impl Fn(T) -> bool` parameter — left to the
generator to pick per §12's "do not invent behaviour" rule applied to implementation
*style*, not semantics: whichever is chosen must have both overloads call into one shared
body, per D13's fusion mandate (no duplicated per-idiom logic).

## 6. `Machine<P: Params>` — fields, constructor, methods

```rust
pub struct Machine<P: Params> {
    pub mg: Vec<Vec<Option<P::Piece>>>,
    pub p: P::Piece,
    pub py: i64,
    pub px: i64,
    pub pr: u8,
    pub gameover: bool,
    pub cleared_lines: i64,
}
```

`cleared_lines` records how many lines the **last** fix cleared (`0` at `new`);
`move_piece`/`rotate_piece` carry it through unchanged, `fix_piece` overwrites it.

`Machine::new(p: P::Piece, piece_source: impl FnMut() -> P::Piece) -> Self` ≙ `Init p`.
Sets `py := P::initial_y(p)`, `px := P::initial_x(p)`, `pr := 0`, `gameover :=
intersect(P::forbidden_grid(), P::FY, P::FX, &mg, 0, 0)`, `cleared_lines := 0`. `mg` is
built cell-by-cell from `P::initial_main_grid()` (D1, never aliasing the constant):
`false` → `None`; `true` → `Some(piece_source())`, calling `piece_source` once per
occupied cell, in row-major order. `InitialMainGrid`'s Rocq codomain is `bool`; `mg`'s
`Option<Piece>` widening has no canonical piece to attach to a cell that starts occupied,
so the caller supplies one per cell. Which piece a preset occupied cell ends up holding is
never read by any engine logic (only `Option::is_some()` is), so this is lossless and
`piece_source`'s choices never affect correctness. `piece_source` is never actually
invoked for any currently-shipped instance, since every one's `InitialMainGrid` is
entirely `false`. Does **not** call `check_axioms::<P>()` — axioms constrain parameters,
not state, so they are checked once by the program before the first `Machine<P>` of any
given `P` is constructed, never here (skill §5.1). `CHECK_INVARIANTS`-gated `type_ok`
assertion at the end, as in every method below.

Methods take `&mut self` and return `bool` (`true` = action fired, `false` = guard failed
= stutter). Every method's guard is written as a direct transcription of `T1.v`'s own
guard, not a hand-simplified equivalent.

`move_piece(&mut self, dy: i64, dx: i64) -> bool` ≙ `MovePiece (dy,dx)`. Guard:
`!self.gameover && can_move_piece(dy, dx, self)`. On failure: return `false`, no field
touched. On success: `self.py += dy; self.px += dx;` return `true`.

`rotate_piece(&mut self, cw: bool) -> bool` ≙ `RotatePiece cw`. `pr2 :=
(self.pr as i64 + if cw {-1} else {1}).rem_euclid(4) as u8` (D4). Guard:
`!self.gameover && valid(&self.mg, self.p, self.py, self.px, pr2)`. On success:
`self.pr = pr2;` return `true`.

`fix_piece(&mut self, p_new: P::Piece) -> bool` ≙ `FixPiece p_new`. Guard:
`!self.gameover && !can_move_piece(-1, 0, self)`, written via the `can_move_piece` call
(not the reduced `!valid(...)` form) for textual fidelity to the spec. `mg` is uniquely
owned by `Machine` and no alias to its pre-overlay contents survives past this call, so
`GridUnion`, `ClearFullLines`, and `FullLineCount` are realized in place rather than as
three fresh-`Vec` constructions (D13, skill §3.2):

```rust
impl<P: Params> Machine<P> {
    // idiom (3), fused: overlay the current piece directly onto self.mg (§4) —
    // O(PW²), never a fresh HM×WM grid.
    fn overlay_piece(&mut self) {
        let pg = P::rot_grid(self.p, self.pr);
        for dy in 0..P::PW {
            for dx in 0..P::PW {
                if let Some(piece) = pg[dy as usize][dx as usize] {
                    let (gy, gx) = (self.py + dy, self.px + dx);
                    if gy >= 0 && gx >= 0 {
                        let (gy, gx) = (gy as usize, gx as usize);
                        if gy < self.mg.len() && gx < self.mg[0].len() {
                            self.mg[gy][gx] = Some(piece);
                        }
                    }
                }
            }
        }
    }

    pub fn fix_piece(&mut self, p_new: P::Piece) -> bool {
        if self.gameover || can_move_piece(-1, 0, self) { return false; }
        if CHECK_INVARIANTS { assert!(P::piece_all().contains(&p_new)); }   // D5

        self.overlay_piece();

        // FullLineCount, fused: count on the overlaid grid — this is `u`.
        self.cleared_lines = self.mg.iter()
            .filter(|row| is_full_row(row, Option::is_some))
            .count() as i64;

        // ClearFullLines, fused: swap-partition, no drop/alloc for any row (§4).
        let mut write = 0;
        for read in 0..self.mg.len() {
            if !is_full_row(&self.mg[read], Option::is_some) {
                if write != read { self.mg.swap(write, read); }
                write += 1;
            }
        }
        for row in &mut self.mg[write..] {
            row.fill(None);
        }

        self.p = p_new;
        self.py = P::initial_y(p_new);
        self.px = P::initial_x(p_new);
        self.pr = 0;
        self.gameover = intersect(P::forbidden_grid(), P::FY, P::FX, &self.mg, 0, 0);

        if CHECK_INVARIANTS { check_invariants(self); }
        true
    }
}
```

Field-assignment order matches read dependencies (skill §4b): the overlay loop and the
two clearing passes read `self.p`/`self.pr`/`self.py`/`self.px` before any of them are
reassigned to `p_new`'s values; `self.gameover`'s recomputation reads the already-cleared
`self.mg`. No field is read after being overwritten anywhere in this method.

`fall_step(&mut self, p_new: P::Piece) -> bool` ≙ `FallStep`. Disjoint-guard sequencing:
try `self.move_piece(-1, 0)`; if that returns `false` (blocked below, and only then —
`can_move_piece(-1,0,·)`'s failure is exactly `fix_piece`'s guard, `proofs.md` §5), call
`self.fix_piece(p_new)` instead. Exactly one of the two guards holds whenever
`!self.gameover` (`proofs.md` §5's disjoint-guard lemma, skill §6.4), so this is not an
`if`/`else` "try both defensively" — it's the direct sequencing the mutual exclusion
licenses.

`check_axioms::<P>()` — one `assert!` per conjunct of each `Axiom` block, **except**
every `Contained` conjunct (D-Contained) and D8's finiteness/disjointness conjuncts
(skill §4h). Called once, explicitly, before any `Machine<P>` is constructed for a given
`P` — never from `Machine::new` (skill §5.1; see §7). Every `assert!` carries a message
naming the conjunct and the offending value(s) (piece, rotation, dimension, as
applicable) — `check_axioms` is the one function whose failure a *user* debugs from a
raw panic (a malformed `Params` impl at startup), not a test author from a failing
`#[test]`, so a bare `assert!(cond)` with no context would cost real time to diagnose.

- `AxiomsPW`: `P::PW > 0`.
- `AxiomsInitialYX` (∀ `p` in `P::piece_all()`): `1 - P::PW <= P::initial_y(p) &&
  P::initial_y(p) < HM` and similarly for `initial_x`/`WM`.
- `AxiomsRotGrid` (∀ `p`, ∀ `r ∈ 0..4`): `P::rot_grid(p,r)` is `PW×PW` with `≥1` occupied
  cell; at `r=0`: `fully_contained_in(P::rot_grid(p,0), P::initial_y(p), P::initial_x(p),
  P::forbidden_grid(), P::FY, P::FX)`.
- `AxiomsInitialMainGrid`, `AxiomsForbiddenGrid`: shape/containment checks, minus their
  `Contained` conjuncts (D-Contained).
- D10 headroom: `std::cmp::max(hm, wm) <= i64::MAX - P::PW + 1` — rearranged so no
  intermediate step can itself overflow (`max(hm,wm) + PW - 1 <= i64::MAX` would panic on
  overflow in a debug build and be vacuously true after silently wrapping in release,
  checking nothing in either profile). Vacuous for this instance, checked for every
  instantiation regardless — skill §5.3.

`type_ok<P: Params>(s: &Machine<P>) -> bool` — rectangular `HM×WM` `mg`, each cell `None`
or `Some` of a `P::piece_all()` member; integral `pr ∈ 0..4` (enforced by type `u8` plus
an explicit range check, since `u8` alone doesn't bound it to `<4`);
`P::piece_all().contains(&s.p)`.

`check_invariants<P: Params>(s: &Machine<P>)` (D7) — mirrors `Correct`'s five conjuncts
exactly, calling `type_ok(s)` rather than re-implementing it.

`Machine<P>` needs no bespoke `snapshot` function: rendering takes `&Machine<P>` directly
(D-Rust2, skill §3.1); `Machine<P>: Clone` (derivable, since every field is `Clone`)
covers the rare case something needs an owned, frozen copy.

**Helpers for refining models.** `new_piece_state`, `new_piece_yx_state`,
`new_main_grid_gameover_state` (§3, §5) — placed in a trailing `model.rs` section of the
same name as `T1.v`'s own, after `check_invariants`, not as `Machine` methods. Each
mutates the given `s: &mut Machine<P>`'s corresponding fields in place and touches nothing
else: `new_piece_state` sets `p`/`py`/`px`/`pr` (`py`/`px` from `P::initial_y`/`initial_x`
of the new piece, `pr := 0`); `new_piece_yx_state` sets `py`/`px` only; `new_main_grid_gameover_state`
sets `mg`/`gameover` only.

## 7. Const flags

`const CHECK_AXIOMS: bool = true;` — never read by `model.rs` itself; the program's entry
point (§15) is responsible for calling `check_axioms::<Instance>()` behind this flag,
exactly once, before constructing any `Machine<Instance>` (skill §5.1). A naive
`static`/`Once`-based "already checked" memoization inside `check_axioms`'s own body must
not be used: a `static` declared inside a generic function is not monomorphized per type
parameter, so a shared `Once` would silently skip axiom-checking for every `P` after the
first one checked (skill §5.1).

`const CHECK_INVARIANTS: bool = false;`

Module-level in `model.rs`: none of `HM`/`WM`/`B` are compile-time constants (they are
derived from the runtime `Params::initial_main_grid()` per D12/D10); they are recomputed
from `self.mg.len()`/`self.mg[0].len()` at each use site that needs them — `Machine`
carries no extra fields beyond `T1.v`'s own state (§6).

## 8. `proofs.md` — required structure (frozen order)

Follows the `rocq-to-rust` skill's `proofs.md` skeleton (skill §6) exactly: scope, state
mapping α with the homomorphism conditions and per-field `⟦_⟧` coercions (skill §6.1),
helper lemmas (skill §6.2), each action (skill §6.3), disjunctive actions (skill §6.4),
the `type_ok` coupling invariant (skill §6.5), box-determinism (skill §6.6),
integer-range safety (skill §6.7). Two T1-specific obligations beyond the generic
skeleton:
- §6.7's bound `B` is stated and proved directly against `T1.v`'s `InitialMainGrid`/`PW`
  (D10) — there is no external bounds file to cite.
- §6.2 must include the **extensional** equivalence lemmas for `GridUnion`,
  `ClearFullLines`, and `FullLineCount` as realized inside `Machine::fix_piece` (§4, §6),
  including the ordering clause the swap-partition's equivalence to `ClearFullLines`
  requires (skill §4f, §3.2).

## 9. Tests — required suites

`tests/test_instance.rs` provides `TestInstance`, a `Params` impl distinct from
`instance::Tetris`: `PW = 3` (exercising that the engine isn't hardcoded to `PW = 4`), a
6×5 board, a 2-row forbidden zone (`FY = 4, FX = 0`), spawn at `(InitialY, InitialX) =
(3, 1)`, and two pieces — `Bar` (a straight 3-cell piece, `r0 = r2`/`r1 = r3` by symmetry)
and `Corner` (an L-tromino, all four rotations distinct). The small board makes
line-clearing scenarios (§9.1) easy to hand-construct and keeps property/fuzz traces
(§9.2/§9.3) fast; every occupied cell of both pieces' `r = 0` grids satisfies
`AxiomsRotGrid`'s spawn-containment conjunct against this forbidden zone. The same file
also provides `Prng`, a fixed-seed xorshift64 used by §9.2–§9.4 in place of a
`rand`-family dependency, for what is in each of those suites just "pick one of a few
small integers many times"; a fixed seed makes every run reproducible without needing to
log one.

Rust `#[test]` modules:

### 9.1 Unit (`model_unit_test.rs`) — deterministic golden vectors
`rot_grid` (4 rotations, identity under 4× application on the occupied set);
`fix_piece`'s line-clearing behaviour (empty/one-full-bottom/middle/top/several/all/none,
asserted on `mg`/`cleared_lines` after the call, since `clear_full_lines` is not a
separate function — §4/§6); `intersect`/`occupied_inside`/`valid` at every boundary
(negative offset, `=H`, `=W`, including the negative-`usize`-cast pitfall of skill §4g);
`rem_euclid` (`(-1i64).rem_euclid(4) == 3`, full `{-1..4}` table); `move_piece`/
`rotate_piece`/`fix_piece`/`fall_step` guard and success cases.

### 9.2 Property-based (`model_properties_test.rs`, e.g. `proptest`)
`type_ok` after every step; `mg` stays `HM×WM`; `check_invariants` passes; no panic (D9);
every integer field within `±B`; gameover monotonicity; a cleared row's buffer is reused,
not reallocated, across a `fix_piece` call (property specific to the swap-partition
realization, §4/§6).

### 9.3 Fuzz (`model_fuzz_test.rs`)
Long random traces (10³–10⁵ steps); assert no panic + `type_ok` + bounds +
gameover-monotone after each step. Adversarial `check_axioms`: malformed instance params
must trip an assertion, not pass silently.

### 9.4 Differential refinement oracle (`oracle.rs`)
A literal interpreter of `T1.v` (hand-written or extracted), whose grids are materialized
on `[Y g, Y g+H g) × [X g, X g+W g)`; for each step of a random trace, assert the Rust
`Machine<P>`'s state ≡ `materialize(rocq_next(event, rocq_state))`.

## 10. Acceptance oracle (operational check, not the definition of correctness)

1. `model.rs` compiles under `#![deny(warnings)]`; no `unsafe`.
2. Coverage check: every `Definition`/`Fixpoint`/`Axiom`/`Record` name in `T1.v` is either
   in the §3 map, explicitly listed as not-emitted with reason, or covered by the fusion
   rule (§4).
3. All §9 suites pass; §9.4 passes if present.
4. `proofs.md` contains every §8 item.
5. Regeneration diff vs. the committed golden snapshot is empty up to §3's naming map and
   comment text.

## 11. Instantiation (`instance.rs`, runtime input)

Not generated by the T1 codegen pipeline; generated separately (§13). Must implement
`Params` (§2) satisfying the four `Axiom` blocks (minus their `Contained` clauses,
D-Contained) and `B <= i64::MAX`. `Piece` is a finite `Copy + Eq` enum (D8);
`check_axioms::<Instance>()` validates once, at program start (§7, §15), not at
`Machine::<Instance>::new(...)`.

## 12. Generator determinism rules

Temperature 0 (refinement-preserving equivalence across regenerations, not textual
identity); single pass; reference `T1.v` by name; emit in the frozen orders (§3, §8); no
invented behaviour/optimisations/APIs; stop and surface a TODO on unresolved ambiguity,
rather than guessing. Any main-loop state that changes across frames (`machine`,
`key_held`, `repeat_timers`, §15) is a field of a local owned by `main`'s loop body, never
a `static`.

---

## 13. `instance.rs` — concrete Tetris parameters

### 13.1 Scalar parameters

| parameter | value |
|-----------|-------|
| `PW` | `4` |
| `HM` (derived) | `22` |
| `WM` (derived) | `10` |
| `FY` | `20` |
| `FX` | `0` |
| `initial_y(p)` | `19` for every piece |
| `initial_x(p)` | `3` for every piece |

### 13.2 Piece set

```rust
#[derive(Copy, Clone, PartialEq, Eq, Debug, strum::EnumIter)]
pub enum Piece { I, O, T, S, Z, J, L }

impl Piece {
    pub fn all() -> &'static [Piece] {
        use strum::IntoEnumIterator;
        static ALL: std::sync::LazyLock<Vec<Piece>> =
            std::sync::LazyLock::new(|| Piece::iter().collect());
        ALL.as_slice()
    }
}
```

An enum, not a string array (D8): `Copy + Eq` are derived, and matching against `Piece` is
exhaustiveness-checked by the compiler (skill §4h). The enumeration itself is derived
(`strum::EnumIter`) rather than hand-written as a parallel `const ALL: [Piece; 7]` array:
a hand-written list duplicates the variant list and can silently fall out of sync if a
variant is ever added — `check_axioms`'s `∀ p in P::piece_all()` conjuncts (§6) would
then stop covering the missing variant without any compile or runtime error. Deriving
from the enum definition removes that hazard at the cost of one small dependency.

### 13.3 Grid constants

```rust
pub fn initial_main_grid() -> &'static Vec<Vec<bool>> { /* 22×10 all-false, built once */ }
pub fn forbidden_grid()    -> &'static Vec<Vec<bool>> { /* 2×10 all-true, built once */ }
```

`InitialMainGrid` is `22×10` all-`false`, Rocq origin `(0,0)` by representation (D15);
`ForbiddenGrid` is `2×10` all-`true`, Rocq origin `(20,0)`, represented as this array plus
`FY`/`FX`.

### 13.4 `rot_grid` — exact rotated piece grids (all 28)

Coordinates `(y, x)` throughout this section are the `4×4` piece grid's own local
indices: `y = 0` is the bottom row, `y = 3` the top row (D3); `x = 0` is the left
column, `x = 3` the right column.

All 28 grids (7 pieces × 4 rotations) are given directly, as explicit literals — not
derived from a rotation formula or a per-piece rotation center. Any relationship between
a piece's four rotations (e.g. that they trace out a rigid rotation of one another) is a
property of the chosen shapes, not something the representation computes or enforces;
each grid stands on its own and is checked independently against `AxiomsRotGrid` (§13.6).

**All 28 grids.** `[[Option<Piece>; 4]; 4]`, `g[y][x]`:

```rust
const O_R0: [[Option<Piece>; 4]; 4] = [
    [None, None          , None          , None],
    [None, Some(Piece::O), Some(Piece::O), None],
    [None, Some(Piece::O), Some(Piece::O), None],
    [None, None          , None          , None],
];

const I_R0: [[Option<Piece>; 4]; 4] = [
    [None          , None          , None          , None],
    [Some(Piece::I), Some(Piece::I), Some(Piece::I), Some(Piece::I)],
    [None          , None          , None          , None],
    [None          , None          , None          , None],
];

const I_R1: [[Option<Piece>; 4]; 4] = [
    [None, Some(Piece::I), None, None],
    [None, Some(Piece::I), None, None],
    [None, Some(Piece::I), None, None],
    [None, Some(Piece::I), None, None],
];

const I_R2: [[Option<Piece>; 4]; 4] = [
    [None          , None          , None          , None],
    [None          , None          , None          , None],
    [Some(Piece::I), Some(Piece::I), Some(Piece::I), Some(Piece::I)],
    [None          , None          , None          , None],
];

const I_R3: [[Option<Piece>; 4]; 4] = [
    [None, None, Some(Piece::I), None],
    [None, None, Some(Piece::I), None],
    [None, None, Some(Piece::I), None],
    [None, None, Some(Piece::I), None],
];

const T_R0: [[Option<Piece>; 4]; 4] = [
    [None          , None          , None          , None],
    [None          , Some(Piece::T), None          , None],
    [Some(Piece::T), Some(Piece::T), Some(Piece::T), None],
    [None          , None          , None          , None],
];

const T_R1: [[Option<Piece>; 4]; 4] = [
    [None          , None          , None, None],
    [None          , Some(Piece::T), None, None],
    [Some(Piece::T), Some(Piece::T), None, None],
    [None          , Some(Piece::T), None, None],
];

const T_R2: [[Option<Piece>; 4]; 4] = [
    [None          , None          , None          , None],
    [None          , None          , None          , None],
    [Some(Piece::T), Some(Piece::T), Some(Piece::T), None],
    [None          , Some(Piece::T), None          , None],
];

const T_R3: [[Option<Piece>; 4]; 4] = [
    [None, None          , None          , None],
    [None, Some(Piece::T), None          , None],
    [None, Some(Piece::T), Some(Piece::T), None],
    [None, Some(Piece::T), None          , None],
];

const S_R0: [[Option<Piece>; 4]; 4] = [
    [None          , None          , None          , None],
    [None          , Some(Piece::S), Some(Piece::S), None],
    [Some(Piece::S), Some(Piece::S), None          , None],
    [None          , None          , None          , None],
];

const S_R1: [[Option<Piece>; 4]; 4] = [
    [None          , None          , None, None],
    [Some(Piece::S), None          , None, None],
    [Some(Piece::S), Some(Piece::S), None, None],
    [None          , Some(Piece::S), None, None],
];

const S_R2: [[Option<Piece>; 4]; 4] = [
    [None          , None          , None          , None],
    [None          , None          , None          , None],
    [None          , Some(Piece::S), Some(Piece::S), None],
    [Some(Piece::S), Some(Piece::S), None          , None],
];

const S_R3: [[Option<Piece>; 4]; 4] = [
    [None, None          , None          , None],
    [None, Some(Piece::S), None          , None],
    [None, Some(Piece::S), Some(Piece::S), None],
    [None, None          , Some(Piece::S), None],
];

const Z_R0: [[Option<Piece>; 4]; 4] = [
    [None          , None          , None          , None],
    [Some(Piece::Z), Some(Piece::Z), None          , None],
    [None          , Some(Piece::Z), Some(Piece::Z), None],
    [None          , None          , None          , None],
];

const Z_R1: [[Option<Piece>; 4]; 4] = [
    [None          , None          , None, None],
    [None          , Some(Piece::Z), None, None],
    [Some(Piece::Z), Some(Piece::Z), None, None],
    [Some(Piece::Z), None          , None, None],
];

const Z_R2: [[Option<Piece>; 4]; 4] = [
    [None          , None          , None          , None],
    [None          , None          , None          , None],
    [Some(Piece::Z), Some(Piece::Z), None          , None],
    [None          , Some(Piece::Z), Some(Piece::Z), None],
];

const Z_R3: [[Option<Piece>; 4]; 4] = [
    [None, None          , None          , None],
    [None, None          , Some(Piece::Z), None],
    [None, Some(Piece::Z), Some(Piece::Z), None],
    [None, Some(Piece::Z), None          , None],
];

const L_R0: [[Option<Piece>; 4]; 4] = [
    [None          , None          , None          , None],
    [None          , None          , Some(Piece::L), None],
    [Some(Piece::L), Some(Piece::L), Some(Piece::L), None],
    [None          , None          , None          , None],
];

const L_R1: [[Option<Piece>; 4]; 4] = [
    [None          , None          , None, None],
    [Some(Piece::L), Some(Piece::L), None, None],
    [None          , Some(Piece::L), None, None],
    [None          , Some(Piece::L), None, None],
];

const L_R2: [[Option<Piece>; 4]; 4] = [
    [None          , None          , None          , None],
    [None          , None          , None          , None],
    [Some(Piece::L), Some(Piece::L), Some(Piece::L), None],
    [Some(Piece::L), None          , None          , None],
];

const L_R3: [[Option<Piece>; 4]; 4] = [
    [None, None          , None          , None],
    [None, Some(Piece::L), None          , None],
    [None, Some(Piece::L), None          , None],
    [None, Some(Piece::L), Some(Piece::L), None],
];

const J_R0: [[Option<Piece>; 4]; 4] = [
    [None          , None          , None          , None],
    [Some(Piece::J), None          , None          , None],
    [Some(Piece::J), Some(Piece::J), Some(Piece::J), None],
    [None          , None          , None          , None],
];

const J_R1: [[Option<Piece>; 4]; 4] = [
    [None          , None          , None, None],
    [None          , Some(Piece::J), None, None],
    [None          , Some(Piece::J), None, None],
    [Some(Piece::J), Some(Piece::J), None, None],
];

const J_R2: [[Option<Piece>; 4]; 4] = [
    [None          , None          , None          , None],
    [None          , None          , None          , None],
    [Some(Piece::J), Some(Piece::J), Some(Piece::J), None],
    [None          , None          , Some(Piece::J), None],
];

const J_R3: [[Option<Piece>; 4]; 4] = [
    [None, None          , None          , None],
    [None, Some(Piece::J), Some(Piece::J), None],
    [None, Some(Piece::J), None          , None],
    [None, Some(Piece::J), None          , None],
];
```

Each `r = 0` grid has exactly 4 occupied cells, all at `y ∈ {1, 2}`, satisfying
`AxiomsRotGrid`'s spawn-containment conjunct against `InitialYX = (19, 3)` and
`ForbiddenGrid` at `(FY, FX) = (20, 0)` (§13.6): `19 + y ∈ {20, 21} ⊂ [20, 22)` for every
occupied cell, for every piece.

`O`'s four grids are identical (`O_R1`/`O_R2`/`O_R3` are not separately emitted; `rot_grid`
returns `&O_R0` for `O` regardless of `r`, §13.4's table below) — a property of the chosen
shape, not enforced by the representation. Every other piece's four grids are pairwise
distinct.

`rot_grid` is backed by a `[Piece; 7] × [u8; 4]` table, each entry one of the 28 literals
above (or, for `O`, `O_R0` repeated), converted to `Vec<Vec<Option<Piece>>>` and stored
behind a `std::sync::LazyLock` (or equivalent one-time-init cell), so every call returns a
`&'static` reference into that table (§2) — no per-call allocation.

### 13.5 Piece colours

Used by `view.rs`.

```rust
pub fn piece_color(p: Piece) -> [f32; 4] {   // macroquad Color-compatible RGBA, 0.0–1.0
    match p {
        Piece::I => [0x83 as f32 / 255.0, 0xa5 as f32 / 255.0, 0x98 as f32 / 255.0, 1.0],
        Piece::O => [0xfa as f32 / 255.0, 0xbd as f32 / 255.0, 0x2f as f32 / 255.0, 1.0],
        Piece::T => [0xd3 as f32 / 255.0, 0x86 as f32 / 255.0, 0x9b as f32 / 255.0, 1.0],
        Piece::S => [0xb8 as f32 / 255.0, 0xbb as f32 / 255.0, 0x26 as f32 / 255.0, 1.0],
        Piece::Z => [0xfb as f32 / 255.0, 0x49 as f32 / 255.0, 0x34 as f32 / 255.0, 1.0],
        Piece::J => [0x45 as f32 / 255.0, 0x85 as f32 / 255.0, 0x88 as f32 / 255.0, 1.0],
        Piece::L => [0xfe as f32 / 255.0, 0x80 as f32 / 255.0, 0x19 as f32 / 255.0, 1.0],
    }
}
```

A color-per-piece mapping is instance data, unaffected by the render target's color type.

### 13.6 Axiom verification (must be checked at generation time)

| Axiom | check |
|-------|-------|
| `AxiomsPW` | `PW=4>0` ✓ |
| `AxiomsInitialYX` | `1-4=-3 ≤ 19 < 22` and `-3 ≤ 3 < 10` for all pieces ✓ |
| `AxiomsRotGrid` | all 28 grids `4×4` with ≥1 occupied cell ✓; spawn containment for all 7 ✓ |
| `AxiomsInitialMainGrid` | `22×10`, no full line (all-`false`) ✓ |
| `AxiomsForbiddenGrid` | `2×10` all-`true`; `bbox_inside_bbox(ForbiddenGrid,20,0,InitialMainGrid,0,0)`: `20+2-1=21≤21`, `0+10-1=9≤9` ✓ |
| D10 | `B = max(22,10)+4-1 = 25 ≪ i64::MAX` ✓ |

---

## 14. `view.rs` — renderer

`macroquad` is the rendering library this document targets: a pure-Rust, dependency-free
2D game framework providing windowing, an immediate-mode drawing API, keyboard input, and
audio, built on `winit`/`wgpu`, with first-class support for Linux/macOS/Windows (and
WASM). It requires no system library installation, unlike bindings to a C/C++ engine —
relevant given `main.rs`'s only other dependency is `gilrs` (§15.1) for gamepad input,
which `macroquad` doesn't bundle itself.

### 14.1 Public API

```rust
pub fn render<P: Params>(
    constants: &RenderConstants,
    machine: &Machine<P>,
    piece_color: impl Fn(P::Piece) -> [f32; 4],
) { … }
```

`RenderConstants { hm, wm, pw, fy, fx, fh, fw }` is extracted once in `main.rs` from
`Params` and `Machine::new`'s output (read-only; never written back to the engine).
`view.rs` never imports `instance.rs`; it takes `piece_color` as a closure. `machine` is
taken by `&Machine<P>` (D-Rust2, skill §3.1): no snapshot, no clone, `render` reads the
live struct directly, once per frame, under an immutable borrow that coexists with
nothing mutating it concurrently (macroquad's loop is single-threaded, so this borrow is
trivially sound, not merely convenient).

`Layout`, `compute_layout`, `BG_COLOR`, `GAME_OVER_TEXT_COLOR`, `GAME_OVER_BG_COLOR`, and
the grid-drawing sub-procedures (`draw_block`, `draw_background`, `draw_grid_lines`,
`draw_grid`, `draw_piece`) are `pub`: a wrapper layer (`t2`, and through it `t3`) reuses
them directly on its own inner `Machine<P>`/embedded `Layout` field instead of redefining
a parallel copy (skill §7, `t2/implementation.md` §14.1). `cell_origin` and
`draw_game_over` stay private — nothing outside this file calls `cell_origin` directly
(every caller reaches grid cells through the `pub` procedures above), and
`draw_game_over` is T1-specific: it fills the whole window with macroquad's built-in
bitmap font, no panel to exclude and no loaded `Font`, unlike any layer with a side panel.

### 14.2 Layout / scaling, 14.3 coordinate transform

Computed against the window size macroquad reports each frame
(`macroquad::window::screen_width()`/`screen_height()`), and centered on both axes
(D-Grid-Centering): `cell_size` is the largest cell that fits the window's width and its
*margin-reduced* height (`VERTICAL_MARGIN_FRACTION = 0.05` of window height reserved off
the top and, equally, off the bottom — no horizontal counterpart); whichever axis has
slack left over beyond that (window aspect ratio ≠ grid aspect ratio, or the grid is
width-bound and there's spare vertical room inside the margin-reduced band) is centered
by an `(origin_x, origin_y)` offset — the top-left pixel of the grid, added to every
pixel coordinate the renderer computes. `Layout { cell_size, origin_x, origin_y }` — a
`pub` struct with `pub` fields, so a wrapper layer's own `Layout` can embed one as its
base geometry — is computed once per frame (`compute_layout(constants)`, also `pub`) and
threaded by `&Layout` into every draw sub-procedure that needs pixel coordinates (§14.4)
— never recomputed per cell.

```
margin_y      = screen_height() * VERTICAL_MARGIN_FRACTION
usable_height = screen_height() - 2.0 * margin_y
cell_size     = f32::min(screen_width() / wm as f32, usable_height / hm as f32)
origin_x      = (screen_width()  - wm as f32 * cell_size) / 2.0
origin_y      = margin_y + (usable_height - hm as f32 * cell_size) / 2.0
cell_origin(y, x, hm, layout) =
  ( layout.origin_x + x as f32 * layout.cell_size
  , layout.origin_y + (hm - 1 - y) as f32 * layout.cell_size )
```

### 14.4 Sub-procedures (`pub` except `cell_origin`/`draw_game_over`)

Five draw steps, using macroquad's immediate-mode `draw_rectangle`/`draw_line`/
`draw_text`. `main.rs`'s per-frame `clear_background` call handles the whole-window clear,
so `draw_background` here only needs to paint the forbidden-zone rectangle. `draw_block`,
`draw_background`, `draw_grid_lines`, `draw_grid`, and `draw_piece` are `pub` (§14.1); only
`cell_origin` (used solely inside these procedures) and `draw_game_over` (T1-specific,
§14.1) stay private:

```
draw_background(constants, layout)   — forbidden-zone rect only (window clear is main.rs's job)
draw_grid_lines(constants, layout)
draw_block(cx, cy, cell_size, color)
draw_grid(mg, constants, layout, piece_color)   — each locked cell in its own piece's color
draw_piece(machine, constants, layout, piece_color)
draw_game_over(cell_size)   — only if machine.gameover; overlay covers the whole window,
                               not just the grid, so it needs no origin offset
```

Call order: `draw_grid` (locked blocks) → `draw_background` (forbidden-zone tint) →
`draw_grid_lines` → `draw_piece` → `draw_game_over` if applicable.

---

## 15. `main.rs` and `misc.rs` — entry point and shared primitives

### 15.1 Cargo dependencies

```toml
[dependencies]
macroquad = "0.4"
gilrs = "0.11"
strum = { version = "0.26", features = ["derive"] }
```

`gilrs` is a cross-platform gamepad-input crate (Linux/macOS/Windows, via each OS's
native controller API) — `macroquad` covers keyboard but not gamepads, hence the separate
dependency (§14). `strum` supplies the `EnumIter` derive backing `Piece::all()` (§13.2).

(Exact versions to be pinned at generation time against whatever is current — this file
fixes the *architecture*, not a version lockfile.)

### 15.2 `misc.rs` — primitives shared by every crate's `main.rs`

`main.rs` is a binary crate, not linkable from any other crate (§2): a constant, type, or
free function with no dependency on any `ti::model::Machine<P>`'s shape, and needed by more
than one crate's `main.rs`, is declared `pub` in `t1/src/misc.rs` instead and imported —
`t2`'s (and `t3`'s/`t4`'s) own `main.rs` reuse it rather than re-declaring it. `Action` and
its dispatch (`fire`) stay out: `T3.v` adds a sixth action (`Hold`), so `t3/implementation.md`
§15 defines its own `Action` in `t3::misc` reusing these items, and each crate's `fire` is a
free function over its own `Machine<P>` (§15.5) — nothing here calls into any `Machine<P>`.

`DAS_DELAY = 170ms`, `ARR = 50ms` (D17):

```rust
pub const DAS_DELAY: f64 = 0.170;
pub const ARR: f64 = 0.050;
```

Window/platform setup (D-Window). Fullscreen at startup; `Esc` (checked in each crate's own
main loop, §15.4) is the only way out, since a fullscreen window has no title-bar close
button:

```rust
pub fn window_conf() -> Conf {
    Conf { window_title: "Tetris".to_owned(), fullscreen: true, ..Default::default() }
}
```

`LogicalKeys` — layout-independent key resolution (D-Logical-Keys). Cw/Ccw bind to
whichever physical key currently produces the logical letters `x`/`z` under the *system*
keyboard layout, not to a fixed `KeyCode`: macroquad's `KeyCode` enum reflects a fixed
physical-key mapping on at least some platforms/backends, so binding directly to
`KeyCode::X`/`KeyCode::Z` fires on the wrong physical key whenever the system layout
differs from the one that mapping assumes. `get_char_pressed()`'s character queue is
OS-translated on every platform macroquad targets, so it is used to *discover*, at
runtime, which physical `KeyCode` currently produces each logical letter; that discovered
`KeyCode` is then what `is_key_down`/`is_key_pressed` are called with — `get_char_pressed()`
itself is never used for held-state or repeat logic, since (unlike `is_key_down`) it does
not reliably distinguish a genuine second press from the OS's own text-input auto-repeat:

```rust
#[derive(Default)]
pub struct LogicalKeys {
    pub cw: Option<KeyCode>,
    pub ccw: Option<KeyCode>,
}

impl LogicalKeys {
    pub fn update(&mut self) {
        let pressed_now = get_keys_pressed();   // HashSet<KeyCode>
        while let Some(c) = get_char_pressed() {
            if pressed_now.len() == 1 {
                let kc = *pressed_now.iter().next().expect("len() == 1 checked above");
                match c.to_ascii_lowercase() {
                    'x' => self.cw = Some(kc),
                    'z' => self.ccw = Some(kc),
                    _ => {}
                }
            }
        }
    }
}
```

Reads `get_keys_pressed()`'s `HashSet<KeyCode>` directly (checking `.len() == 1` rather
than collecting it into a `Vec` first) — macroquad already allocates that `HashSet`
internally on every call; collecting it into a second collection just to check its size
would be a second allocation for no benefit.

Only updates a binding when exactly one physical key was newly pressed this frame
(`pressed_now` — `get_keys_pressed()`, edge-triggered) *and* that frame's character
queue contains `'x'`/`'z'` (either case): an ambiguous frame (zero or several
simultaneous new presses) leaves the existing binding untouched, so a key held down
elsewhere can never corrupt a binding already learned. Left/Right/Down stay on the fixed
physical arrow keys (§15.5's table) — arrows aren't letter keys, so they're unaffected
by the layout differences `LogicalKeys` exists to handle, and binding them by discovery
would only add a one-frame delay before the very first press for no benefit.

`update()` is called once per frame, before `process_input` (§15.4): `Action::key`
(§15.5) reads `logical.cw`/`logical.ccw` directly, so Cw/Ccw have no binding at all —
`is_held`/`just_pressed` both report `false` — until their logical letter has been
observed once.

`RepeatTimer` — the DAS/ARR bookkeeping entry (§15.5):

```rust
pub struct RepeatTimer {
    pub pressed_at: f64,
    pub last_fire: f64,
}

impl RepeatTimer {
    pub fn new(now: f64) -> Self {
        RepeatTimer { pressed_at: now, last_fire: now }
    }
}
```

`random_piece::<P>()` — `Instance::piece_all()[macroquad::rand::gen_range(0,
Instance::piece_all().len())]`, generalized over `P` to match every caller's own
genericity:

```rust
pub fn random_piece<P: Params>() -> P::Piece {
    let all = P::piece_all();
    all[macroquad::rand::gen_range(0usize, all.len())]
}
```

`Action` — one input action, `T1.v`'s five (D17); every crate through `T2.v` drives its
`Machine<P>` with exactly this set:

```rust
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub enum Action {
    Left, Right, Down, Cw, Ccw,
}

impl Action {
    pub const ALL: [Action; 5] = [Action::Left, Action::Right, Action::Down, Action::Cw, Action::Ccw];

    pub fn repeats(self) -> bool {
        matches!(self, Action::Left | Action::Right | Action::Down)
    }

    pub fn key(self, logical: &LogicalKeys) -> Option<KeyCode> {
        match self {
            Action::Left => Some(KeyCode::Left),
            Action::Right => Some(KeyCode::Right),
            Action::Down => Some(KeyCode::Down),
            Action::Cw => logical.cw,
            Action::Ccw => logical.ccw,
        }
    }

    pub fn gamepad_button(self) -> Button {
        match self {
            Action::Left => Button::DPadLeft,
            Action::Right => Button::DPadRight,
            Action::Down => Button::DPadDown,
            Action::Cw => Button::East,   // button 1
            Action::Ccw => Button::South, // button 0
        }
    }

    pub fn is_held(self, logical: &LogicalKeys, pad: Option<Gamepad<'_>>) -> bool {
        self.key(logical).is_some_and(is_key_down) || pad.is_some_and(|p| p.is_pressed(self.gamepad_button()))
    }

    pub fn just_pressed(self, logical: &LogicalKeys, pad: Option<Gamepad<'_>>) -> bool {
        self.key(logical).is_some_and(is_key_pressed) || pad.is_some_and(|p| p.is_pressed(self.gamepad_button()))
    }
}

pub fn any_action_just_pressed(logical: &LogicalKeys, pad: Option<Gamepad<'_>>) -> bool {
    Action::ALL.iter().any(|a| a.just_pressed(logical, pad))
}
```

Bindings (D17), covering exactly `T1.v`'s five actions:

| Action                          | Keyboard                       | Gamepad     | Repeats |
|----------------------------------|--------------------------------|-------------|---------|
| move piece left                  | left arrow                     | left d-pad  | yes     |
| move piece right                 | right arrow                    | right d-pad | yes     |
| move piece down                  | down arrow                     | down d-pad  | yes     |
| rotate piece clockwise           | logical `x` (D-Logical-Keys)   | button 1    | no      |
| rotate piece counter-clockwise   | logical `z` (D-Logical-Keys)   | button 0    | no      |

"Logical `x`/`z`" means whichever physical key currently produces that character under
the system keyboard layout, resolved at runtime by `LogicalKeys` above — not a fixed
`KeyCode`. Gamepad "button `N`" follows the standard controller ordering (`gilrs::Button`):
button 0 = `South`, button 1 = `East`.

`fire` is deliberately **not** a method on `Action`: `Action` is shared across crates
(here, and again in `t3::misc` from `T3.v` on), but its dispatch target — which
`ti::model::Machine<P>` to call, and with what argument shape — is genuinely per-crate
(`t4::model::Machine::fall_step` takes a bag, not a single piece, §15.5 of
`t4/implementation.md`). Each crate's own `main.rs` defines a free `fn fire<P: Params>
(action: Action, machine: &mut Machine<P>)` instead (§15.5).

### 15.3 Initialisation

```rust
type Instance = instance::Tetris;   // the concrete Params impl

let constants = RenderConstants {
    hm: Instance::initial_main_grid().len() as i64,
    wm: Instance::initial_main_grid()[0].len() as i64,
    pw: Instance::PW,
    fy: Instance::FY, fx: Instance::FX,
    fh: Instance::forbidden_grid().len() as i64,
    fw: Instance::forbidden_grid()[0].len() as i64,
};
```

### 15.4 `main()` — macroquad entry point

`FALL_PERIOD_SECS = 1.0` (D16). The window opens fullscreen and `Esc` quits (D-Window),
via `t1::misc::window_conf` (§15.2).

```rust
use t1::misc::{random_piece, window_conf, Action, LogicalKeys, RepeatTimer, ARR, DAS_DELAY};

#[macroquad::main(window_conf)]
async fn main() {
    if CHECK_AXIOMS { check_axioms::<Instance>(); }   // once, before touching Instance (§7)

    let mut machine = Machine::<Instance>::new(random_piece::<Instance>(), random_piece::<Instance>);
    let mut key_repeat: HashMap<Action, RepeatTimer> = HashMap::new();
    let mut logical_keys = LogicalKeys::default();
    let mut gilrs = match gilrs::Gilrs::new() {
        Ok(g) => Some(g),
        Err(e) => { eprintln!("gamepad support disabled ({e}); continuing keyboard-only"); None }
    };
    let mut last_fall = macroquad::time::get_time();

    loop {
        if is_key_pressed(KeyCode::Escape) {
            macroquad::miniquad::window::order_quit();
            return;   // window teardown isn't necessarily immediate (D-Window)
        }

        logical_keys.update();   // spec: §15.2, D-Logical-Keys
        if let Some(g) = &mut gilrs {
            while g.next_event().is_some() {}   // drain; state is read via gilrs.gamepad(id), not the event stream
        }
        let pad = gilrs.as_ref().and_then(|g| g.gamepads().next()).map(|(_, pad)| pad);
        process_input(&mut machine, &mut key_repeat, &logical_keys, pad);

        let now = macroquad::time::get_time();
        if now - last_fall >= FALL_PERIOD_SECS {
            machine.fall_step(random_piece::<Instance>());
            last_fall = now;
        }

        render(&constants, &machine, |p: Piece| piece_color(p));
        next_frame().await;
    }
}
```

The `#[macroquad::main(...)]` attribute macro must name a bare function identifier in
scope, not a qualified path (`misc::window_conf` fails to compile with "not a function":
the macro's expansion calls the token as a bare function-call expression); hence
`window_conf` is imported by name rather than referenced as `misc::window_conf`.

State lives in `main`'s async-fn locals (`machine`, `key_repeat`, `logical_keys`, `gilrs`,
`last_fall`), never in a `static` (§12).

No separate "waiting for restart" flag: `machine.gameover` is monotone once `true` (every
`T1.v` transition guards on `!gameover`), so it alone gates both the overlay (§14.4) and
the restart check below.

`Esc` is checked with `is_key_pressed` (edge-triggered, fires once) rather than
`is_key_down`, so holding it doesn't attempt to quit every frame. `Esc` is a fixed
physical `KeyCode`, not resolved through `LogicalKeys` (D-Logical-Keys) — it isn't a
letter key, so it isn't affected by the AZERTY/QWERTY-style layout differences
`LogicalKeys` exists to handle (§15.2). `macroquad::miniquad::window::order_quit()` is
reached through macroquad's own re-export of `miniquad` (`pub use miniquad;` at the
macroquad crate root) — no separate `miniquad` line in `Cargo.toml` (§15.1).

`gilrs::Gilrs::new()` failing (missing udev rules, no permissions, no joystick subsystem
on the host, …) leaves `gilrs := None` for the rest of the run rather than aborting
startup: gamepad support is optional by design (D17 — keyboard alone is a complete input
path), so an environment without a working joystick subsystem must not prevent the game
from starting keyboard-only. The first connected pad, if any, is looked up **once per
frame** (`gilrs.as_ref().and_then(|g| g.gamepads().next())`) and passed down as
`pad: Option<Gamepad<'_>>` — `Gamepad<'_>` is `Copy`, so every `Action` reads the same
per-frame lookup rather than each independently re-querying `Gilrs` (§15.5).

### 15.5 `fire`/`process_input` — dispatch and the merged held-state + shared DAS engine

Keyboard read via `macroquad::input::is_key_down` on each action's *currently bound*
physical key (fixed for Left/Right/Down, resolved through `LogicalKeys` for Cw/Ccw —
§15.2, D-Logical-Keys), gamepad via `gilrs::Gamepad::is_pressed` on
`pad: Option<Gamepad<'_>>` — the first connected pad, looked up **once per frame** by the
caller (§15.4) and passed down, rather than each action independently re-querying
`Gilrs` — merged into one `held: HashMap<Action, bool>`.

Effects:

```
move piece left/right: move_piece(0, ∓1)
move piece down:       fall_step(random_piece())
rotate cw/ccw:          rotate_piece(true) / rotate_piece(false)
```

```rust
fn fire<P: Params>(action: Action, machine: &mut Machine<P>) {
    match action {
        Action::Left => { machine.move_piece(0, -1); }
        Action::Right => { machine.move_piece(0, 1); }
        Action::Down => { machine.fall_step(random_piece::<P>()); }
        Action::Cw => { machine.rotate_piece(true); }
        Action::Ccw => { machine.rotate_piece(false); }
    }
}

fn process_input<P: Params>(
    machine: &mut Machine<P>,
    repeat: &mut HashMap<Action, RepeatTimer>,
    logical: &LogicalKeys,
    pad: Option<gilrs::Gamepad<'_>>,
) {
    if machine.gameover {
        if any_action_just_pressed(logical, pad) { *machine = Machine::new(random_piece::<P>(), random_piece::<P>); }
        repeat.clear();
        return;
    }
    let now = macroquad::time::get_time();
    for action in Action::ALL {
        let is_held = action.is_held(logical, pad);
        match repeat.entry(action) {
            Entry::Vacant(e) => {
                if is_held { fire(action, machine); e.insert(RepeatTimer::new(now)); }
            }
            Entry::Occupied(mut e) => {
                if !is_held {
                    e.remove();
                } else if action.repeats() && now - e.get().pressed_at >= DAS_DELAY && now - e.get().last_fire >= ARR {
                    fire(action, machine);
                    e.get_mut().last_fire = now;
                }
                // else: held, but either non-repeating (already fired once, waiting
                // for release) or repeating and still within the DAS/ARR window
            }
        }
    }
}
```

`fire` is a free function, not a method on `Action` — see §15.2's own note on why `Action`
excludes it. `process_input` itself is not shared via `t1::misc`, even though its shape is
identical in every crate through `T2.v`: it is the one place a `Controller`-style trait
over every `ti::model::Machine<P>` was considered and deliberately rejected — `T4.v`'s
`fall_step`/`hold_piece` take a bag (`&[P::Piece]`) rather than a single piece, so a shared
dispatch trait cannot be written without either breaking at `t4` or generalizing the trait
around a difference that is genuine model behavior, not incidental duplication. Each
crate's `main.rs` therefore keeps its own `process_input`, reusing only the primitives
above that don't touch `fire`'s or `Machine::new`'s shape.

`repeat.entry(action)` (`std::collections::hash_map::Entry`) replaces a `.get()` to
decide the branch followed by a separate `.get_mut()`/`.insert()`/`.remove()` to act on
it: `Entry` does the one hash lookup up front, and both the `Vacant`/`Occupied` arms
read/mutate/insert/remove through that same handle — no redundant second lookup, and no
`.unwrap()` needed to re-fetch what the match already found. `action.repeats()` inside
the `Occupied` arm folds the repeating/non-repeating split into the same match (a
non-repeating action held with an existing entry just falls through to the trailing
comment-only case — its "already fired" marker stays put until release, matching the
original repeats()-outer-if structure exactly, verified case-by-case: `Vacant` + held →
fire + insert on both; `Occupied` + not held → remove on both; `Occupied` + held +
repeating + DAS/ARR elapsed → fire + update `last_fire` on both; every other
`Occupied` + held case → no-op on both).

`Action::key(self, logical: &LogicalKeys) -> Option<KeyCode>` is the one point that reads
`LogicalKeys`: `Some(KeyCode::Left/Right/Down)` for the three move actions, `logical.cw`/
`logical.ccw` for Cw/Ccw (`None` until discovered, §15.2). `is_held`/`just_pressed` both
route through it: `self.key(logical).is_some_and(is_key_down)` (respectively
`is_key_pressed`), `||`-combined with the gamepad reading.

Semantics: fire once on press, then DAS-delay before auto-repeat; non-repeating actions
fire once per press.

### 15.6 Window resize

Not needed: macroquad reports the live window size every frame
(`screen_width()`/`screen_height()`), so `view.rs`'s `cell_size` computation (§14.2)
already tracks window resizes with no separate resize handler or cached dimensions to
maintain.
