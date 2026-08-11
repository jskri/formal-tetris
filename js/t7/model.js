import { T as T6 } from '../t6/model.js';

const CHECK_AXIOMS = true;
const CHECK_INVARIANTS = false;

// spec: module T7 (parameters: T1-T6's, then Player, HostIndex, then defaulted
// MAX_SAFE_INTEGER). t7/model.js implements PlayerCount > 1 only — single-player
// uses t6/model.js directly, selected by the controller before any t7.Machine
// exists (implementation.md §0).
export function T(
  Piece, InitialMainGrid, ForbiddenGrid,
  RotGrid, InitialY, InitialX,
  PW, FY, FX,
  NextLen,
  Player, HostIndex,
  MAX_SAFE_INTEGER = Number.MAX_SAFE_INTEGER,
) {
  const T6Eng = T6(Piece, InitialMainGrid, ForbiddenGrid, RotGrid, InitialY, InitialX,
                    PW, FY, FX, NextLen, MAX_SAFE_INTEGER);
  const T1Eng = T6Eng.T1Eng; // flattened

  const HM = InitialMainGrid.length;
  const WM = InitialMainGrid[0].length;
  const PlayerCount = Player.length;
  const Host = Player[HostIndex];

  // spec: PlayerNext — Player values are plain indices
  const PlayerNext = (i) => (i + 1) % PlayerCount;

  // no PlayerEqb, compared with ===

  // ── Free functions (§5) ───────────────────────────────────────────────

  // spec: PlayingView s pl pl2 — pl's own view of pl2's playing status.
  // No observer parameter: a Machine only ever evaluates its own views (§4-T7b).
  function playingView(gameoverView, connectedView, pl2) {
    return !gameoverView[pl2] && connectedView[pl2];
  }

  // spec: WinnerMulti s pl
  function winnerMulti(gameoverView, connectedView, myIndex) {
    for (let pl2 = 0; pl2 < PlayerCount; pl2++) {
      if (playingView(gameoverView, connectedView, pl2) !== (pl2 === myIndex)) return false;
    }
    return true;
  }

  // spec: NextTargetAux / NextTarget — first successor of `pl` that `playing`
  // reports true for and that isn't `self`; returns `self` if none is found
  // within one full cycle (the winner case — req-multi-target-nonself).
  function nextTarget(playing, self, pl) {
    let cur = pl;
    for (let i = 0; i < PlayerCount; i++) {
      cur = PlayerNext(cur);
      if (playing(cur) && cur !== self) return cur;
    }
    return self;
  }

  // spec: GeneratedGarbage clearedLines perfectClear
  function generatedGarbage(clearedLines, perfectClear) {
    const c = clearedLines;
    const normalGarbage = c < 4 ? Math.max(0, c - 1) : c; // nat subtraction, floors at 0
    const specialGarbage = perfectClear ? 10 : 0;
    return normalGarbage + specialGarbage;
  }

  // spec: GenRemGarbage garbage clearedLines perfectClear
  function genRemGarbage(garbage, clearedLines, perfectClear) {
    const genGarbage = generatedGarbage(clearedLines, perfectClear);
    const remGarbage = Math.max(0, garbage - genGarbage); // nat subtraction
    return [genGarbage, remGarbage];
  }

  // One materialized garbage row: `w` cells, occupied except at column `hole`.
  // No direct T7.v counterpart — GarbageGrid's per-row content, realized directly
  // for the array representation instead of as a Grid record (§4-T7c).
  // Occupied cells are stamped 'garbage', not `true` — mg's cell type is
  // false | Piece | 'garbage' at this layer (D1/D8, t1/model.js); view.js's
  // pieceColor[cell] ?? gray fallback already renders an unrecognized key
  // distinctly, no special-casing needed there.
  function garbageRow(hole, w) {
    return Array.from({ length: w }, (_, x) => x !== hole ? 'garbage' : false);
  }

  // ── Axiom checker ─────────────────────────────────────────────────────
  function checkAxioms() {
    T6Eng.checkAxioms();
    console.assert(Piece.every(p => p !== 'garbage'),
      "AxiomsGarbageSentinel: no Piece may equal 'garbage' (t7/model.js's materialization sentinel)");
    console.assert(Number.isInteger(PlayerCount) && PlayerCount > 1,
      'AxiomsPlayer: PlayerCount must be > 1 (t7/model.js is MP-only)');
    console.assert(Number.isInteger(HostIndex) && 0 <= HostIndex && HostIndex < PlayerCount,
      'AxiomsHost: HostIndex must be a valid index into Player');
  }

  function checkInvariants(s, message, isOccupied = (c => Piece.includes(c) || c === 'garbage')) {
    T6Eng.checkInvariants(s.s6, message, isOccupied);
    console.assert(
      Number.isInteger(s.myIndex) && 0 <= s.myIndex && s.myIndex < PlayerCount,
      `myIndex range failed @ ${message}`);
    console.assert(
      Number.isInteger(s.garbage) && s.garbage >= 0 && s.garbage <= MAX_SAFE_INTEGER,
      `garbage range failed @ ${message}`);
    console.assert(
      Number.isInteger(s.target) && 0 <= s.target && s.target < PlayerCount,
      `target range failed @ ${message}`);
    console.assert(s.gameoverView.length === PlayerCount,
      `gameoverView length failed @ ${message}`);
    console.assert(s.gameoverView.every(c => typeof c === 'boolean'),
      `gameoverView contains non-booleans @ ${message}`);
    console.assert(s.connectedView.length === PlayerCount,
      `connectedView length failed @ ${message}`);
    console.assert(s.connectedView.every(c => typeof c === 'boolean'),
      `connectedView contains non-booleans @ ${message}`);
    console.assert(s.remGenGarbage >= 0, `remGenGarbage >= 0 failed @ ${message}`);
    // Addition:
    console.assert(s.s6.gameover === s.gameoverView[s.myIndex],
      `s6.gameover and gameoverView[myIndex] do not agree @ ${message}`);
  }

  // ── Machine: encapsulates T7.State ───────────────────────────
  class Machine {
    // spec: Init bags H
    constructor(myIndex, bagsFn) {
      this.s6 = new T6Eng.Machine(bagsFn);       // spec: T6.Init (bags myIndex) (H myIndex)
      this.myIndex = myIndex;
      this.garbage = 0;
      this.target = PlayerNext(myIndex);
      this.gameoverView = Array(PlayerCount).fill(false);
      this.gameoverView[myIndex] = this.s6.gameover; // SelfViewAccurate at Init
      this.connectedView = Array(PlayerCount).fill(true);
      this.remGenGarbage = 0;
      if (CHECK_INVARIANTS) checkInvariants(this, 'Init');
    }

    // spec: WinnerMulti s myIndex, memoized as a getter — read by every guarded method
    get winner() {
      return winnerMulti(this.gameoverView, this.connectedView, this.myIndex);
    }

    // Read-through getters — every field controller.js reads directly outside
    // snapshot(). `gameover`/`level`/`combo`/`perfectClear`/`totalClearedLines`
    // are promoted at T4/T5/T6 level too (confirmed against t5/model.js's own
    // getter list); `score`/`hold`/`next_` are not, anywhere in the tower —
    // nothing needs them live. T1-level-only fields (`mg`, `clearedLines`,
    // `p`, `py`, `px`, `pr`) are reachable solely via the flattened `s1`
    // accessor, never a direct `this.s6.<field>`. `p`/`py`/`px`/`pr` exist
    // here specifically for `broadcastState()` (controller.js): reading them
    // live avoids constructing a full snapshot() (which spreads through the
    // whole T1–T6 chain and copies fields this call never uses) just to throw
    // most of it away — safe because `JSON.stringify`, the only consumer,
    // never mutates what it's given, unlike view.js, which is why snapshot()
    // wraps `mg` read-only in the first place.
    get level() { return this.s6.level; }
    get combo() { return this.s6.combo; }
    get perfectClear() { return this.s6.perfectClear; }
    get totalClearedLines() { return this.s6.totalClearedLines; }
    get score() { return this.s6.score; }
    get gameover() { return this.s6.gameover; }
    get mg() { return this.s6.s1.mg; }
    get clearedLines() { return this.s6.s1.clearedLines; }
    get p() { return this.s6.s1.p; }
    get py() { return this.s6.s1.py; }
    get px() { return this.s6.s1.px; }
    get pr() { return this.s6.s1.pr; }
    get gy() { return this.s6.gy; }

    // spec: MovePiece pl dyx — full use, delegate to s6
    movePiece(dy, dx) {
      if (this.winner) return false;
      const fired = this.s6.movePiece(dy, dx);
      if (CHECK_INVARIANTS) checkInvariants(this, 'movePiece');
      return fired;
    }

    // spec: RotatePiece pl cw — full use, delegate to s6
    rotatePiece(cw) {
      if (this.winner) return false;
      const fired = this.s6.rotatePiece(cw);
      if (CHECK_INVARIANTS) checkInvariants(this, 'rotatePiece');
      return fired;
    }

    // spec: HoldPiece pl bagNew H — full use, delegate to s6
    holdPiece(bagNew) {
      if (this.winner) return false;
      const fired = this.s6.holdPiece(bagNew);
      if (CHECK_INVARIANTS) checkInvariants(this, 'holdPiece');
      return fired;
    }

    // spec: RotateKickPiece pl cw — full use, delegate to s6
    rotateKickPiece(cw) {
      if (this.winner) return false;
      const fired = this.s6.rotateKickPiece(cw);
      if (CHECK_INVARIANTS) checkInvariants(this, 'rotateKickPiece');
      return fired;
    }

    // spec: FixPiece pl holes H1 bagNew H2 — §4-T7c/d
    fixPiece(bagNew, holesFn) {
      if (this.winner) return false;

      const fired = this.s6.fixPiece(bagNew); // full T6 semantics first
      if (!fired) return false;

      const s1 = this.s6.s1; // mg/clearedLines are T1-level only — never promoted as
                              // getters anywhere in the tower (unlike gameover/level/
                              // combo/perfectClear/totalClearedLines, which are)
      const [genGarbage, remGarbage] = genRemGarbage(
        this.garbage, s1.clearedLines, this.s6.perfectClear);
      const remGenGarbage = Math.max(0, genGarbage - this.garbage); // req-multi-garbage-cancel

      // Materialization — unconditional (no PlayerCount === 1 branch, never
      // reached here). remGarbage is unbounded (garbage accumulates with no
      // cap via receiveGarbage), so it can exceed HM — effRem clamps it; the
      // Grid algebra T7.v uses handles this for free via an unbounded
      // function cropped to box, the array representation needs the clamp
      // explicitly to avoid a negative scan index / unbounded array growth.
      const effRem = Math.min(remGarbage, HM);

      let gameover2 = this.s6.gameover;
      if (!gameover2 && remGarbage > 0) {
        let overflow = remGarbage >= HM; // pushes the entire board off — no scan needed
        if (!overflow) {
          for (let y = HM - remGarbage; y < HM; y++) {
            if (s1.mg[y].some(T1Eng.occ)) { overflow = true; break; }
          }
        }
        gameover2 = overflow;
      }

      // shift always runs, regardless of gameover2 — the stored grid always
      // reflects materialization, whatever caused gameover2. Decreasing i:
      // a destination index (i + effRem) can coincide with a later source
      // index, so increasing order would read an already-overwritten row.
      if (effRem > 0) {
        for (let i = HM - effRem - 1; i >= 0; i--) s1.mg[i + effRem] = s1.mg[i];
        for (let y = 0; y < effRem; y++) s1.mg[y] = garbageRow(holesFn(y), WM);
        // this.s6.fixPiece(bagNew) above already spawned the new piece and
        // computed gy (T5's updateShadowY) against the pre-materialization
        // grid. Splicing garbage rows in just now shifted that grid out from
        // under it, so gy is stale until recomputed against the new s1.mg.
        this.s6.updateShadowY();
      }

      if (!gameover2) {
        gameover2 = T1Eng.intersect(ForbiddenGrid, FY, FX, s1.mg, 0, 0); // on the new mg
      }
      s1.gameover = gameover2; // gameover is getter-only at every level above T1

      this.garbage = 0; // remaining garbage is consumed by being materialized
      this.remGenGarbage = remGenGarbage;
      this.gameoverView[this.myIndex] = gameover2; // SelfViewAccurate

      if (remGenGarbage > 0 && !gameover2) {
        // req-multi-garbage-send: the target becomes its first successor that
        // is playing, per pl's own (just-updated) view.
        const view = (pl2) => playingView(this.gameoverView, this.connectedView, pl2);
        this.target = nextTarget(view, this.myIndex, this.target);
      }

      if (CHECK_INVARIANTS) checkInvariants(this, 'fixPiece');
      return true;
    }

    // spec: FallStep pl holes H1 bagNew H2
    fallStep(bagNew, holesFn) {
      if (this.winner) return false;
      if (this.movePiece(-1, 0)) return true; // req-piece-fall
      return this.fixPiece(bagNew, holesFn);  // req-piece-fix
    }

    // spec: DropPiece pl holes H1 bagNew H2 s := FixPiece pl holes H1 bagNew H2
    // (NewPieceYXState (gy s pl, px s pl) pl s). Relocates to the shadow
    // position (px unchanged) exactly as t5/model.js's own dropPiece does (same
    // s1 field copy), then calls T7's own fixPiece instead of T6's — so garbage
    // generation/cancellation/materialization/target-redirect isn't bypassed on
    // a hard drop.
    dropPiece(bagNew, holesFn) {
      if (this.winner) return false;
      T6Eng.T4Eng.assertPieceSet(bagNew); // defensive, before any mutation — mirrors t5/model.js
      if (this.gameover) return false;
      const s1 = this.s6.s1;
      const r = T1Eng.newPieceYXState(this.s6.gy, s1.px, s1);
      s1.mg = r.mg;
      s1.p = r.p;
      s1.py = r.py;
      s1.px = r.px;
      s1.pr = r.pr;
      s1.gameover = r.gameover;
      s1.clearedLines = r.clearedLines;
      return this.fixPiece(bagNew, holesFn); // guaranteed to fire, given LowestShadowY
    }

    // spec: NoticeDisconnection pl — locally-detected own link-to-host
    // failure, called by this player's own controller (§4-T7g). Not gated on
    // `winner`: a player who just became the winner can still legitimately
    // lose her own connection afterward.
    noticeDisconnection() {
      this.connectedView[this.myIndex] = false;
      if (CHECK_INVARIANTS) checkInvariants(this, 'noticeDisconnection');
    }

    // spec: ReceiveMessage pl from — GarbageMessage branch. No `from`
    // parameter: the state update is sender-agnostic (§4-T7e). Not gated on
    // `winner`/`gameover`: a disconnected/gameover player keeps draining her
    // queues; the value simply sits inert (never read again).
    //
    // T7.v's `garbage` is an exact, unbounded ℕ; clamped here at
    // MAX_SAFE_INTEGER like every other accumulator in the tower (e.g. score),
    // rather than left to silently lose precision past 2^53. garbage is
    // drained to 0 on pl's own next materializing fixPiece (§4-T7c), so this
    // only matters for a pathological trace with unboundedly many
    // GarbageMessages arriving between two of pl's own fixes — never reached
    // in an ordinary match, but not excluded by the model either.
    receiveGarbage(amount) {
      this.garbage = (this.garbage <= MAX_SAFE_INTEGER - amount)
        ? this.garbage + amount : MAX_SAFE_INTEGER;
      if (CHECK_INVARIANTS) checkInvariants(this, 'receiveGarbage');
    }

    // spec: ReceiveMessage pl from — GameoverMessage branch. `view` matches
    // T7.v's shared `view'` exactly, including the `from ↦ true` override:
    // that forces NextTargetAux's round-robin to always terminate on a real
    // match — at the latest when it wraps back around to `from` itself —
    // rather than ever falling through to NextTargetAux's own `self`
    // fallback (fuel = 0), which this call must never reach.
    receiveGameover(from) {
      this.gameoverView[from] = true;
      if (this.target === from) {
        const view = (pl2) => playingView(this.gameoverView, this.connectedView, pl2);
        this.target = nextTarget(view, this.myIndex, from);
      }
      if (CHECK_INVARIANTS) checkInvariants(this, 'receiveGameover');
    }

    // spec: ReceiveMessage pl from — DisconnectMessage branch. Same target
    // redirect as GameoverMessage (T7.v uses one shared `view'` for both),
    // with the same `from ↦ true` override — see receiveGameover.
    receiveDisconnect(from) {
      this.connectedView[from] = false;
      if (this.target === from) {
        const view = (pl2) => playingView(this.gameoverView, this.connectedView, pl2);
        this.target = nextTarget(view, this.myIndex, from);
      }
      if (CHECK_INVARIANTS) checkInvariants(this, 'receiveDisconnect');
    }
  } // class Machine

  // spec: snapshot — extends T6's inline
  function snapshot(machine) {
    return {
      ...T6Eng.snapshot(machine.s6),
      garbage: machine.garbage,
      target: machine.target,
      gameoverView: machine.gameoverView.slice(),
      connectedView: machine.connectedView.slice(),
      remGenGarbage: machine.remGenGarbage,
      myIndex: machine.myIndex,
    };
  }

  // Axioms are properties of the closure-captured instance parameters, fixed
  // for the lifetime of this T(...) call — checked once here, not once per
  // `new Machine(...)` (every restart), since they can never fail differently
  // between one construction and the next.
  if (CHECK_AXIOMS) checkAxioms();

  return {
    // free functions (§5)
    playingView,
    winnerMulti,
    nextTarget,
    generatedGarbage,
    genRemGarbage,

    // inner engine
    T6Eng,
    T1Eng, // flattened

    // helpers / invariant checkers
    checkAxioms,
    checkInvariants,

    // machine
    Machine,
    snapshot,
  };
}
