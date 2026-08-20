# implementation.md — `final/`, delta over `t7/implementation.md`

Not a fresh derivation. `final/` introduces no `model.rs` of its own and no
new `Params`/`instance` type — every `T7.v`/`T6.v` correspondence
`t7/implementation.md` already establishes applies unchanged, reached through
the exact same types. This file's own scope is narrower: the crate layout,
and the surface `final/` adds on top of `t7/`'s already-documented behavior —
procedural sound effects, two lock/garbage animations, and a single-player
hall of fame.

## 0. Scope, and what's reused unchanged

`final/` drives two engines, exactly as `t7/main.rs` already does for its own
`App::Single`/`App::Playing` arms:

- **Single-player**: `t6::model::Machine<SingleInstance>` directly — no
  `t7::model::Machine`, no roster, no filler (§0.2/§15 of `t7/implementation.md`:
  `t7::model::Machine::new` asserts `player_count > 1`, so single-player is
  never routed through it at any layer).
- **Multiplayer**: `t7::model::Machine<Instance>`, driven through
  `t7::session::Session` — the lobby/relay/roster state machine
  `t7/implementation.md` documents at §15, promoted to `t7`'s public API
  (tracked separately; not part of this pass — §6 below assumes it).

No `instance.rs`: `final/` calls `t7::instance::Tetris`/`t1::instance::Piece`
directly wherever `t7/main.rs` does. No `model.rs`, no `tests/` — nothing
introduced here is a `Machine`-level primitive with a refinement obligation of
its own; every new module is either pure rendering/audio data or a thin,
independently-testable persistence layer.

## 1. File layout

```
final/
  Cargo.toml           # path deps: t1–t7; new deps: rodio (sfx), directories (hall of fame)
  src/
    main.rs             # game loop + screen state — delta over t7/main.rs (§5)
    sound.rs             # procedural sfx: synthesis + playback, no asset files (§2)
    anim.rs                # clear-flash / garbage-flash / gameover-partial timers + draws (§3)
    highscores.rs            # JSON-file hall of fame, single-player only (§4)
```

## 2. `sound.rs`

Procedural tones only — synthesized at runtime, no audio asset files, no
music. Backend: `rodio` (`OutputStream` + `Sink`), not macroquad's own
`audio` feature — that feature plays back sample files via `quad-snd` and has
no oscillator-synthesis path, and no audio dependency exists anywhere in
`t1`–`t7` today to build on.

- **`Waveform`**: `Sine | Square | Triangle | Sawtooth`.
- **`ToneSpec { waveform, freq_hz, duration, gain, slide_to: Option<f32> }`** —
  one oscillator envelope: linear attack-free onset, exponential gain decay to
  ~0 over `duration`; `slide_to`, when set, exponentially glides `freq_hz`
  toward it over the same span. Mirrors a single Web-Audio
  oscillator+gain-node pair's behavior, restated as a plain data spec instead
  of a live node graph.
- **`render_tone(spec: &ToneSpec, sample_rate: u32) -> Vec<f32>`** — renders
  one spec to a mono sample buffer.
- **`render_chord(specs: &[(f32, ToneSpec)]) -> Vec<f32>`** — each `(offset,
  spec)` pair renders independently and additively mixes into one buffer
  starting at `offset` seconds; used for the handful of multi-tone events
  below (a sequenced arpeggio when offsets are staggered, a simultaneous chord
  when they're all `0.0`).
- **`Sfx`** — an enum naming every trigger: `Move, Rotate, Hold, Fix, Drop,
  Clear(u8), PerfectClear, Combo(u8), LevelUp, Gameover, GarbageSlam(u8),
  Winner, Disconnect, HostLost`. `Clear`/`GarbageSlam`'s payload scales pitch
  and/or duration with the count (a bigger clear or a bigger garbage delivery
  reads as a bigger sound); `Combo`'s payload does the same for a running
  combo streak.
- **`SoundEngine`** — owns the `rodio::MixerDeviceSink`/`Mixer`, a
  `render_tone`/`render_chord`-produced `HashMap<Sfx, rodio::buffer::SamplesBuffer>`
  cache built once at construction (every variant is a fixed, finite set —
  no runtime-generated keys; each buffer's samples live in an internal
  `Arc<[f32]>`, so caching the built `SamplesBuffer` rather than a raw
  `Vec<f32>` makes every `play()` clone an `Arc` refcount bump instead of a
  copy of the sample data), and an `AtomicBool` mute flag.
  - **`play(&self, sfx: Sfx)`** — no-op while muted; otherwise looks up the
    cached buffer and plays a clone of it on a newly-detached `Player`
    (never a shared one) so overlapping triggers — e.g. a move sound firing
    mid-clear-animation — layer instead of cutting each other off.
  - **`toggle_muted(&self)` / `is_muted(&self) -> bool`**.
- One `SoundEngine` instance lives in `main()`'s own local state (constructed
  once, alongside `RunState`), not a global — consistent with everything else
  in this crate's game loop being plain local state, no statics.
- Bound to a new key (`M`), polled the same way escape/menu-nav already are
  in every screen arm of `t7/main.rs`'s loop.

## 3. `anim.rs`

`t7`'s own renderer already recomputes layout and redraws everything from
scratch every frame (`t4::view::compute_layout` is never cached) — timed
overlay animations are a natural extension of that discipline, not a new
pattern requiring its own clock or event system. Both timers below are plain
state carried alongside `RunState` in the caller's frame loop, advanced by the
same `now` (`get_time()`) every other per-frame calculation already uses.

- **`ClearAnim { grid: Vec<Vec<Option<PieceOrExtra>>>, rows: Vec<usize>,
  tetris: bool, start: f64 }`** — armed on a locking action that clears at
  least one line. `grid` is the *placed-but-uncleared* board (this piece's
  cells merged in, at the position/rotation it had the instant before the
  authoritative `fix_piece`/`fall_step`/`drop_piece` call ran) and `rows` are
  the row indices that qualify as full in that grid.

  **Why this is computed locally, not read off `Machine`:** per
  `t7/implementation.md` §4-T7c, `fix_piece` fuses grid-union and line-clearing
  into one step and never exposes the intermediate "placed, not yet cleared"
  grid as a public value — there is nothing to read it off. `final/` therefore
  reconstructs it itself, from the same public inputs the real call is about
  to consume: clone the current `mg`, place the active piece's cells into the
  clone using its current `py`/`px`/`pr` and `P::rot_grid(piece, pr)` (the same
  shape data `fix_piece` itself reads), then find full rows in the clone with
  `t1::model::is_full_row`. This runs immediately **before** the mutating
  call, in the same calling code that's about to invoke `fire`/`fire_single`
  — never inside `t7`/`t6`'s own model code, which stays untouched.
- **Progress curve** — a pure `fn progress(anim: &ClearAnim, now: f64) ->
  f32`: linear ramp to `1.0` over `CLEAR_ANIM_SECS` for a 1–3 line clear;
  for a 4-line (`tetris: true`) clear, over the longer `TETRIS_ANIM_SECS`, a
  curve that reaches white slightly *before* `1.0` and adds a decaying sine
  ripple on top, so a Tetris pulses rather than flatly fades once. Values can
  briefly exceed `1.0` — callers clamp alpha, not the curve itself.
- **`GarbageAnim { row_count: u8, start: f64 }`** — armed only once a locking
  action that materializes pending garbage actually returns (never merely
  "garbage was pending" — the exact row count materialized is read from
  `t7::model::gen_rem_garbage`'s second component, the same free function
  `fix_piece` itself calls internally, given the same pre-call `garbage`
  amount and post-call `cleared_lines`/`perfect_clear`). Sequenced to start
  only after any `ClearAnim` from the same lock has finished — matching the
  model's own sequencing (materialization always follows this player's own
  clear in `fix_piece`'s body), not merely a rendering convenience. Duration
  `GARBAGE_ANIM_SECS`, alpha `1.0 → 0.0` linearly — a hard, fast-cutoff flash,
  deliberately not a fade-in.
- **Screen shake**: `fn shake_offset(amp_px: f32, remaining_frac: f32) ->
  (f32, f32)` — a decaying random offset, applied by the caller as a
  translation of the render origin for the duration of a Tetris clear
  (`TETRIS_SHAKE_PX`) or a garbage arrival (`GARBAGE_SHAKE_PX`, scaled by
  `row_count.min(2)`, since a bigger delivery should read as a harder hit).
  Applied by offsetting the coordinates every draw call for that frame uses —
  there is no separate transform layer to apply it to once, only immediate
  per-call drawing.
- **Draw functions**, each taking already-computed data, never a `Machine` —
  except `draw_board_without_gameover_overlay` below, which genuinely needs
  the live `Machine` since (unlike the other two) it isn't animating any
  transient, precomputed snapshot; it's the ordinary board render with one
  branch skipped:
  - `draw_clear_flash(constants, grid, rows, progress, piece_color, font)` —
    redraws the frozen `grid` (no falling piece — already merged in) via the
    same primitives `t6::view`/`t1::view` already expose, then fills only
    `rows` white at `alpha = progress.clamp(0.0, 1.0)`.
  - `draw_garbage_flash(constants, row_count, progress)` — a flat reddish fill
    over the bottom `row_count` rows at `alpha = 1.0 - progress`.
  - `draw_gameover_partial(constants, font)` — dim overlay + "GAME OVER"
    heading only, omitting whatever restart-prompt line the normal gameover
    render already draws elsewhere — used during the lockout window below.
  - `draw_board_without_gameover_overlay(constants, machine, piece_color,
    banner, font)` — `t5::view::render`'s own body (hold box, panel,
    banners, preview, grid, background, grid lines, ghost, piece), minus
    its trailing gameover-overlay call. Used under `draw_gameover_partial`
    during the lockout window so the frozen board renders without the
    normal gameover overlay, without mutating `machine`'s own `gameover`
    field to dodge that one branch. `t5::view`'s own `draw_ghost` is made
    `pub` for this (`t5/implementation.md` §14.3) — every other primitive
    it calls was already `pub`.
- **Combo / perfect-clear banners are *not* new here.** `t2::view::Banner` /
  `draw_banners` already exist and are already wired into every render call in
  `t7/main.rs`'s own `RunState`/`after_action` (populated whenever
  `total_cleared_lines` increases). `final/` reuses this exactly as-is — no
  new banner code.
- **Gameover lockout — single-player only.** `t7/main.rs`'s multiplayer path
  already has this: `Playing.own_gameover_since` + `GAMEOVER_FILLER_DELAY_SECS`
  delay the S7→S8 filler handoff so a last-second keypress doesn't
  instantly discard the "GAME OVER" frame. `App::Single`'s own gameover
  branch has no such delay — it restarts on the very next
  `any_action_just_pressed`. `final/` adds the identical pattern there (a
  `gameover_since: Option<f64>` local + a `SP_GAMEOVER_LOCKOUT_SECS`
  constant), reusing the existing MP constant's role rather than inventing a
  different mechanism for the second path — see §5.

## 4. `highscores.rs`

Single-player only. Persisted as a JSON file, with a fail-soft contract and
a versioned schema.

- **`Entry { name: String, score: u64, level: u64, lines: u64, date:
  SystemTime }`**, `Vec<Entry>` sorted descending by `score`.
- **`MAX_ENTRIES: usize = 10`.**
- **Storage location**: `directories::ProjectDirs`'s data directory, file
  name `highscores-v1.json` — versioned so a later schema change doesn't have
  to migrate or crash reading old data.
- **`load() -> Vec<Entry>` / `save(&[Entry])`** — private; every filesystem
  call wrapped so a missing directory, permissions failure, or corrupt JSON
  degrades to an empty list / silent no-op rather than panicking. A
  never-created data directory is exactly the "storage disabled" case, not an
  error.
- **`is_storage_available() -> bool`** — a real write-then-read-back probe
  against the actual target path, not merely "does the directory exist" —
  the failure modes that matter (read-only filesystem, out of space,
  sandboxed/no-write environment) only surface on an actual write attempt.
- **`qualifies(entries: &[Entry], score: u64) -> bool`** — true if the table
  has fewer than `MAX_ENTRIES` entries, or `score` beats the current lowest.
- **`record_score(name, score, level, lines) -> Vec<Entry>`** — loads,
  appends, sorts descending, truncates to `MAX_ENTRIES`, persists, returns the
  new list.

## 5. `main.rs` — delta over `t7/main.rs`

Every `sfx`/animation hook below is inserted **strictly after** the mutating
call it reacts to, gated on the same fired/not-fired signal that call already
returns — the identical placement discipline `t7/main.rs` itself already uses
for `after_action`'s own post-call bookkeeping. `ClearAnim`'s precompute (§3)
is the one exception: it runs immediately **before** the mutating call, since
its whole purpose is capturing state that call is about to overwrite.

**Multiplayer (`App::Playing`, built on `t7::session::Session`, §0):**
- Around `playing.session.fire_and_broadcast(|machine| fire(action, machine,
  wm))`: the wrapping closure additionally matches on `action` to trigger
  `Sfx::Move`/`Rotate`/`Hold` unconditionally, and — only when `fire`'s own
  return is `true` — snapshots `machine.garbage`/`mg`/`py`/`px`/`pr` before
  the call for `ClearAnim`'s precompute and `GarbageAnim`'s pre-fix `garbage`
  reading, then after the call fires `Sfx::Fix` or `Sfx::Drop` depending on
  which action ran, plus `Sfx::Clear`/`Sfx::PerfectClear`/`Sfx::Combo` from
  the same `cleared_lines`/`perfect_clear`/`combo` fields `after_action`
  already reads.
- In `after_action`'s existing `s2.level != run.prev_level` branch:
  `Sfx::LevelUp`.
- At the `App::Winner`/`App::HostLost`/own-gameover transitions already
  matched in the frame loop's `outcome` block: `Sfx::Winner` (only when the
  resolved winner is `machine.my_index`), `Sfx::HostLost`, `Sfx::Gameover`
  (on this player's own gameover-view flipping true).
- Disconnect: diff `machine.connected_view` against its previous frame's
  snapshot (a local `Vec<bool>` kept alongside `RunState`) — on any `true →
  false` transition not caused by this player itself, `Sfx::Disconnect`. This
  avoids needing a new hook inside `Session` itself; the view array `t7`
  already exposes is sufficient.
- `GarbageAnim`/`Sfx::GarbageSlam`: computed right after a firing `Down`/`Drop`
  call, from the `garbage` amount snapshotted before the call and
  `cleared_lines`/`perfect_clear` read after it, via `t7::model::gen_rem_garbage`
  (§3) — armed only if its row-count component is nonzero.

**Single-player (`App::Single`, unchanged `t6::model::Machine<SingleInstance>`
path):**
- Same hook shape applied to `fire_single`'s `Action` match and
  `after_action`'s level/clear branches — no `Sfx::GarbageSlam`/`Winner`/
  `Disconnect`/`HostLost` (none apply outside multiplayer).
- Gameover handling gains the lockout described in §3
  (`gameover_since`/`SP_GAMEOVER_LOCKOUT_SECS`), replacing the current
  instant-restart-on-keypress with: draw `draw_gameover_partial` until the
  lockout elapses, then — once elapsed — branch on
  `highscores::is_storage_available() && highscores::qualifies(&entries,
  score)`:
  - **Qualifies**: a new local screen state holding a text-entry buffer
    (reusing the same `TextInput`/`poll_text_edit` machinery
    `t7/main.rs`'s lobby screens already use for name entry), capped at
    `HOF_NAME_MAX_LEN` (20) characters for both typed and pasted input (via
    `TextInput::apply`'s parameterized `max_len`, shared with the lobby
    fields which pass the larger `TEXT_INPUT_MAX_LEN`), and driving the same
    `drive_backspace_repeat`/`RepeatTimer` auto-repeat the lobby name fields
    already use — submitting calls `record_score` and transitions to the
    hall-of-fame display below, highlighting the just-added entry.
  - **Doesn't qualify, or storage unavailable**: skip straight to the
    hall-of-fame display, unhighlighted; if storage is unavailable, the
    display also shows a short "scores can't be saved right now" notice
    instead of silently omitting the feature.
  - The hall-of-fame display lists up to `MAX_ENTRIES` entries in
    fixed-width columns under a header row (rank, name padded to
    `HOF_NAME_MAX_LEN`, score/level/lines right-aligned — the embedded
    monospace font makes this a pure formatting concern). Restarting from
    this screen accepts Enter, Space, or any normal alphanumeric key — not
    arrow/movement keys, which (unlike elsewhere in `App::Single`) do not
    restart from here; Escape, handled one level up unconditionally for
    `App::Single`, returns to mode-select as before.
- `Sfx::Gameover` fires once, at the moment gameover is first observed —
  before the lockout window, not after — matching the multiplayer path's own
  "gameover flips true → fires immediately" timing.