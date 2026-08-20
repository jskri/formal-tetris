# proofs.md — refinement proof, `final/ ⊨ T7.v`

Not a fresh derivation. `final/` introduces no `model.rs` of its own: multiplayer drives
`t7::model::Machine<Instance>` through `t7::session::Session`, single-player (and the shared
mid-match/waiting-room filler) drives `t6::model::Machine<SingleInstance>` directly — the same
two engines `t7/proofs.md` and `t6/proofs.md` already prove refine `T7.v` and `T6.v`
respectively (`t7/proofs.md` §2: `T7.v` reduces definitionally to `T6.v` at `PlayerCount = 1`,
and `t7::model::Machine::new`'s own `assert!(player_count > 1)` makes single-player's regime
the only one the filler/single-player path can ever be in — §9 below). This file's own
obligation is narrower: catalogue everything `final/` adds over `t7`'s and `t6`'s own public
API, and show each addition is *no-use* with respect to the refinement mapping — it never calls
a `Machine`-mutating method beyond the set `t7/proofs.md`/`t6/proofs.md` already cover, in an
order or with arguments that differ from what's already proven there.

## 0. Result

`final/`'s entire new surface — `sound.rs`, `anim.rs`, `highscores.rs`, and
`main.rs`'s own added local state and call sites — is either read-only against
already-computed `Machine` state, or a side effect (audio synthesis/playback, a
JSON file on disk) entirely disjoint from `Σ`. No new call to a mutating
`Machine` method is introduced; no existing one is removed, reordered relative
to another mutating call, or given different arguments. `t7/proofs.md`'s and
`t6/proofs.md`'s own conclusions transfer without modification.

## 1. Scope

Safety only, inherited from `t7/proofs.md` §1 / `t6/proofs.md`'s own scope note. Nothing in
`final/` touches liveness either way.

## 2. No `model.rs` in `final/` — same classes, not wrapped

```
$ ls final/src/
anim.rs  highscores.rs  main.rs  sound.rs
```

No `final/model.rs`, no new `Params`/instance type. `main.rs` imports `t7::model::Machine`
(via `t7::session::{Instance, Session}`), `t7::session::fire`/`fire_and_broadcast`, and
`t7::app::{fire_single, fresh_single, after_action, process_input, step_playing_transition,
SingleInstance, RunState, …}` — the identical classes and free functions `t7/proofs.md` and
`t6/proofs.md` already prove refine `T7.v`/`T6.v`, not subclasses, not wrapped, not
monkey-patched — no projection lemma is needed for any `Machine` method beyond "this is literally
the class/function already proven," because it literally is. This holds one level further down
than the bare `Machine` type itself: `t7::app` is itself `t7/main.rs`'s own screen/dispatch
machinery, promoted to a public library module and reused verbatim
(`implementation.md` §0 of this file: "no `instance.rs`… every new module is
either pure rendering/audio data or a thin, independently-testable persistence layer").
`t7::model::Machine<Instance>`'s and `t6::model::Machine<SingleInstance>`'s own mutating
methods are called only through `t7::session::fire`/`t7::app::fire_single` — themselves pure
dispatchers (`match action { … }`, one arm per `Action`, each calling exactly the method
`t7/main.rs`'s own dispatch already calls, with the same arguments: `shuffle_bag::<P>()` for
the bag, `fresh_holes(wm)` for garbage holes) — not a new mutating primitive of their own.

## 3. `anim.rs` — read-only rendering, precompute reads before the mutating call

`draw_clear_flash`, `draw_garbage_flash`, `draw_gameover_partial`,
`draw_board_without_gameover_overlay`: none takes `&mut Machine` — only `&t6::model::Machine<P>`
(both engines reuse this one function, a caller for `t7::model::Machine<Instance>` passing
`&machine.s6`) or plain data (a raw grid array, row indices, a progress float, a pixel-offset
pair). No mutating method call anywhere in this file — grep-verifiable: `anim.rs` contains no
`&mut t6::model::Machine`/`&mut t7::model::Machine` parameter and no `.fix_piece(`/
`.fall_step(`/`.drop_piece(`/`.move_piece(`/`.rotate_piece(`/`.hold_piece(` call. No-use,
trivially — there is nothing here for `α` to even see.

`precompute_clear` reads `mg`, the active piece's identity, and its position/rotation
(`py`/`px`/`pr`, or `gy` in place of `py` for a `Drop` call — the same shadow-landing row
`drop_piece`'s own relocation, `t7/proofs.md` §7, is about to move the piece to) directly off a
`&Machine` reference, before the mutating call that reference is about to be handed to
(`fire_single_with_effects`/`fire_with_effects`, §7–§8). It reconstructs the "placed, not yet
cleared" grid — the union-then-clear-lines step every `fix_piece` performs internally (inherited
from `t1/proofs.md` through `t6/proofs.md`, reused unchanged inside `t7::model::Machine`'s own
`fix_piece`, `t7/proofs.md` §5) and never exposes as an intermediate value — using
`P::rot_grid`/`t1::model::is_full_row`, the same already-proven query primitives `t1/proofs.md`
covers, not a new placement algorithm. A read before a write cannot itself be the write; the
mutating call immediately following it (§7/§8) is unchanged in argument or position.

## 4. `sound.rs` — side-effecting, disjoint from `Σ`

`SoundEngine`'s cache/mixer/mute flag is private, module-local state — reachable from no
`model.rs`/`session.rs`/`net.rs` code and reaching into none of it (no `Machine`/`Session`
reference is ever passed to any function in this file). Every `sound.play(...)` call site
(catalogued in §7/§8) sits strictly *after* the `Machine`/dispatch call whose outcome it reacts
to has already returned — it reads no `Machine` field and writes none. No-use: `Σ`, as
`t7/proofs.md` §3 defines it (and as `t6/proofs.md`'s own `Machine`-instance-only `Σ` defines
it), has no audio component for this to touch.

## 5. `highscores.rs` — side-effecting, disjoint from `Σ`

`get_high_scores`/`is_storage_available`/`qualifies`/`record_score` operate on `{score, level,
lines}` — three plain `u64`s, read once off `game.machine.s4.s3.s2`'s own `score`/`level`/
`total_cleared_lines` fields *after* `gameover` is already `true` and copied into local
variables — never a `Machine` reference itself — plus a JSON file under the platform's own
per-app data directory (`directories::ProjectDirs`), with a fail-soft contract (a missing
directory, permissions failure, or corrupt file degrades to an empty list / silent no-op).
No-use, the same reasoning as §4: no filesystem component exists in `Σ` either.

## 6. New local state in `App`'s own structs

`Playing`'s own `own_gameover_since` field, and the `Session`/`filler` fields both `Waiting` and
`Playing` already carry, are unchanged — the identical fields `t7::app::step_playing_transition`
already reads/writes and `t7/main.rs`'s own `Playing`/`Waiting` structs already declare (`t7`'s
own doc comment on `own_gameover_since`: gates the `GAMEOVER_FILLER_DELAY_SECS` transition into
`S8`). What's new here is: `SpGame` (a wrapper `t7/main.rs`'s own `App::Single` has no
counterpart for — there, `App::Single` holds a bare `t6::model::Machine<SingleInstance>` with no
extra state at all) and its `clear_anim`/`gameover_since`/`post` fields; `Waiting`'s
`filler_clear_anim`/`filler_gameover_since`; `Playing`'s `filler_clear_anim`/
`filler_gameover_since`/`mp_clear_anim`/`mp_garbage_anim`/`connected_prev`. None of these new
fields is read by `α`. `t7/proofs.md` §3 defines `α` as a function of specific, named fields
(`s6`, `garbage`, `target`, `gameoverView`, `connectedView`, `connected`, `messages`);
`t6/proofs.md`'s own `Σ` is the bare `Machine` instance. Adding fields to `Σ` that `α` never
reads cannot change what `α` computes, by construction — the same reasoning that already lets
`t7/proofs.md`'s own `Σ` (§3 there) include host relay/heartbeat bookkeeping that most individual
`T7.v` events never touch either.

`gameover_since`/`filler_gameover_since` apply the identical lockout-delay *pattern*
`own_gameover_since`/`step_playing_transition` already use for `GAMEOVER_FILLER_DELAY_SECS`, to
two transitions `t7/main.rs`/`t7::app` drive with no delay at all today:
`SP_GAMEOVER_LOCKOUT_SECS` gates single-player's own restart-on-keypress (`App::Single` there
restarts on the very next keypress), `FILLER_GAMEOVER_LOCKOUT_SECS` gates the filler's own
(`t7::app::restart_filler_on_keypress` has no delay of its own either). Delaying *when* a
restart happens doesn't change that it *is* the restart `t6/proofs.md`'s own base case (a fresh
`Init` via `fresh_single()`, §7–§8 below) already covers, whenever it actually runs.

`connected_prev` is read, never written, from `machine.connected_view` (via
`session.opponent_views()`, a read-only accessor `t7/proofs.md` §3 already treats as outside
`Σ`'s own mutation surface) each frame — a diff against last frame's own local copy, feeding
only a sound trigger (§4), touching no `Machine` field.

## 7. Multiplayer (`App::Playing`) — every call site checked

`final/`'s `App::Playing` arm inlines the same shape `t7::app::step_playing_gameplay` already
implements (rather than calling that function directly) for one reason: the gravity tick must
itself go through the sound/anim-decorated dispatch, not a bare `fall_step` call that would
bypass it — a gravity-driven lock is common enough (most locks happen from gravity, not a held
key) that a silent one would make the game read as broken. Checked against every `Machine`- or
`Session`-touching call in the arm:

- **`fire_with_effects`** wraps `t7::session::fire(action, machine, wm, on_result)` — the
  identical function `t7::app::step_playing_gameplay`'s own dispatch call and `t7/main.rs`'s own
  `Playing` arm already call, same arguments (`action`, `machine`, `wm`), same `on_result`
  contract (invoked with each underlying call's real return value, never altering it).
  `sound.play(...)` calls happen from inside `on_result`, gated on `ok` — strictly after each
  `move_piece`/`rotate_piece`/`rotate_kick_piece` (via `t7::session::rotate`, itself unchanged)/
  `hold_piece`/`fall_step`/`drop_piece` call has already returned (§4). `apply_lock_effects` runs
  only once `fire`'s own return is `true`, after `fire` has already returned control — it reads
  `garbage_before` (a `machine.garbage` snapshot taken *before* the `fire` call, i.e. before
  `fix_piece` could touch it) and `machine.s6.cleared_lines()`/`.perfect_clear` (read *after*),
  then calls `t7::model::gen_rem_garbage` — the exact free function `fix_piece` itself calls
  internally on the same inputs (`model.rs`: `fix_piece`'s own
  `gen_rem_garbage(self.garbage, cleared_lines, perfect_clear)`) — reproducing, not altering,
  the same materialization `fix_piece` already computed. No new `Machine` call.
- **`session.fire_and_broadcast(|machine| fire_with_effects(...))`** — the same
  `Session::fire_and_broadcast` `t7/main.rs`'s own `Playing` arm already calls, identical shape
  (samples `was_gameover`/`pre_target`, calls the closure, conditionally calls
  `broadcast_after_fix`): `t7/proofs.md` §8's own one-push-per-successful-fix argument applies
  unchanged, since the closure it wraps here still resolves to exactly one `fire` call per
  invocation, same as `t7/main.rs`'s own bare `fire`.
- **The gravity tick** — `session.fire_and_broadcast(|machine| fire_with_effects(Action::Down,
  ...))`, gated on the identical `now - run.last_fall >= run.current_gravity_period` guard
  `t7::app::step_playing_gameplay`'s own gravity branch uses, same call shape.
- **`process_input(gameover, ..., |action| session.fire_and_broadcast(...))`** — the same
  `t7::app::process_input` free function `step_playing_gameplay`/`t7/main.rs` already call,
  unmodified; only the dispatch closure passed to it differs (sound/anim-decorated, not a
  different function).
- **`after_action(&machine.s6.s4.s3.s2, now, &mut run)`** — the same free function, same
  arguments, `step_playing_gameplay`/`t7/main.rs` already call — read-only against `s2`
  (`score`/`level`/`total_cleared_lines`), used here only to select
  `play_after_action_sfx`'s `Sfx::LevelUp`/`Clear`/`PerfectClear`/`Combo` triggers (§4).
- **Disconnect sfx** diffs `session.opponent_views()` (read-only, §6) against `connected_prev`
  — no `Machine` call.
- **`session.pump(now)`/`session.leave()`** — identical calls, identical arguments, to
  `t7/main.rs`'s own `Playing`/escape arms (`Session`'s network-pump and departure-notify entry
  points, `session.rs`, already argued in `t7/proofs.md` §8/§10).
- **`step_playing_transition(&playing.session, filler_is_none, &mut playing.own_gameover_since,
  ...)`** — the same `t7::app` free function `t7/main.rs`'s own `Playing` arm calls, same
  arguments; `final/` adds only an `sound.play(...)` at each of its four outcome arms
  (`ToWinner`/`ToHostLost`/`GameoverWaitStarted`-first-observed/`EnteredFiller`), strictly after
  the function has already returned its outcome — no-use.
- **`drive_filler(...)`** mirrors `t7::app::drive_filler_input`'s own body (`process_input` over
  a per-action dispatch, then a gravity `fall_step` call gated on the same
  `run.last_fall`/`current_gravity_period` check) plus `restart_filler_on_keypress`'s own
  gameover-and-keypress restart check, kept local rather than calling those two functions
  directly for the same reason the `Playing` arm above is inlined: the gravity tick must itself
  go through `fire_single_with_effects` (§8), so a gravity-driven filler lock still plays
  `Sfx::Fix`/arms `clear_anim`. Every `Machine` call inside — `filler.fall_step(&shuffle_bag::
  <SingleInstance>())` for gravity, plus `fire_single_with_effects`'s own calls (§8) — is the
  identical call `t7::app::drive_filler_input`/`fire_single` itself makes, and the restart
  (`*filler = fresh_single()`) is `t7::app::fresh_single()`, the identical fresh-`Machine`
  construction `restart_filler_on_keypress` itself performs — `t6/proofs.md`'s own base case,
  not a new one.

## 8. Single-player (`App::Single`) and the shared filler — every call site checked

- **`fire_single_with_effects`** wraps `t7::app::fire_single(action, machine, on_result)` — the
  identical function `t7/main.rs`'s own single-player arm already calls, unmodified, same
  arguments. `precompute_clear` (§3) runs before it for an about-to-lock `Down` or every `Drop`,
  reading only `s1` fields off the same `machine` reference `fire_single` is about to mutate.
  `sound.play(...)` calls happen from `on_result`, gated on `ok`, strictly after each underlying
  call has already returned (§4). `clear_anim` is armed only once `fired` is known and the
  precomputed rows are known non-empty — after both `fire_single` and the precompute have
  already run, so nothing here reorders relative to `fire_single`'s own single call.
- **Gravity**: `fire_single_with_effects(Action::Down, ...)` on the same
  `run.last_fall`/`current_gravity_period` guard `t7::app::drive_filler_input`/
  `step_playing_gameplay` already use.
- **`after_action(&game.machine.s4.s3.s2, now, &mut run)`** — same free function, same
  arguments, read-only — feeds `play_after_action_sfx` only (§4).
- **Hall-of-fame hook**: reached only once `gameover` is already `true`
  (`game.gameover_since.is_some()`) and `SP_GAMEOVER_LOCKOUT_SECS` has elapsed — reads
  `game.machine.s4.s3.s2`'s `score`/`level`/`total_cleared_lines` (three plain numbers, copied
  out), calls `highscores::get_high_scores`/`is_storage_available`/`qualifies` (§5) — no
  `Machine` call. The name-entry/submit path (`poll_text_edit`/`drive_backspace_repeat`/
  `TextInput`, `t7::text`) is entirely disjoint from `Σ` — the same machinery the `Host`/`Join`
  lobby text fields already use unchanged, reused here for one more field with a smaller
  `max_len`; its Enter-triggered `record_score` call is the same no-use `highscores` call (§5).
  The Hall-of-Fame screen's own restart (Enter/Space/any alphanumeric key) executes
  `*game = SpGame::fresh()`, whose `machine: fresh_single()` field is `t7::app::fresh_single()`
  — the identical fresh-`Machine` construction §7's filler restart performs, `t6/proofs.md`'s
  own base case again, not a new one.

## 9. `PlayerCount = 1` — discharged by `t6/proofs.md`, never constructed otherwise

`final/`'s single-player path (`App::Single`, and the shared filler used by `Waiting`/`S8`)
never touches `t7::model::Machine` at all — it is `t6::model::Machine<SingleInstance>`
throughout, the same regime `t7/proofs.md` §2 already discharges in full
(`t7::model::Machine::new`'s own `assert!(player_count > 1)` makes this the only regime
single-player can ever be in). Nothing in §§3–8 above depends on which regime is active at a
given call site — every read-only or side-effecting addition is argued against whichever
`Machine` reference is actually in play there, with the corresponding proof (`t7/proofs.md` for
multiplayer, `t6/proofs.md` for single-player) doing the refinement work underneath.

## 10. Conclusion

`final/`'s obligation reduces entirely to `t7/proofs.md` (multiplayer, `App::Playing`/
`Waiting`) and `t6/proofs.md` (single-player, `App::Single` and the shared filler), verbatim,
plus §§3–8 above showing every addition — `sound.rs`, `anim.rs`, `highscores.rs`, and `main.rs`'s
own new local state and call sites — is no-use: no new `Machine`-mutating call is introduced, no
existing one is removed, reordered relative to another mutating call, or given different
arguments. `final/ ⊨ T7.v` (multiplayer) and `final/ ⊨ T6.v` (single-player, via `T7.v`'s own
`PlayerCount = 1` delegation, `t7/proofs.md` §2) both hold.
