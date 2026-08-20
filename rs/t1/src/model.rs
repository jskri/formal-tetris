//! spec: T1
//!
//! The T1 engine: piece move/rotation, line clearing, gameover. Generic over
//! `Params`, the trait carrying `T1.v`'s abstract parameters (`Piece`,
//! `InitialMainGrid`, `ForbiddenGrid`, `RotGrid`, `InitialYX`, `PW`).
//!
//! D1: pure-boolean grids are `Vec<Vec<bool>>`; `mg` and `RotGrid`'s output
//! are `Vec<Vec<Option<_>>>` (`None` = empty). Grid arrays use local origin
//! `(0, 0)`; a non-zero Rocq origin (`ForbiddenGrid`) is carried separately
//! as `y`/`x` arguments.

// ── Axiom/invariant checker flags ──────────────────────────────────────────
pub const CHECK_AXIOMS: bool = true;
pub const CHECK_INVARIANTS: bool = false;

// ── Params: T1.v's abstract parameters ─────────────────────────────────────
pub trait Params {
    // spec: Piece
    type Piece: Copy + Eq + std::fmt::Debug + 'static;

    // No `T1.v` counterpart — a higher layer's extra cell content (see
    // `PieceOrExtra` below); unused through T6 (`CellExtra = Infallible`).
    type CellExtra: Copy + Eq + std::fmt::Debug + 'static;

    // spec: PW
    const PW: i64;
    // spec: ForbiddenGrid's YX (D15)
    const FY: i64;
    const FX: i64;

    // finite enumeration of `Piece` (D8)
    fn piece_all() -> &'static [Self::Piece];
    // spec: InitialMainGrid
    fn initial_main_grid() -> &'static Vec<Vec<bool>>;
    // spec: ForbiddenGrid
    fn forbidden_grid() -> &'static Vec<Vec<bool>>;
    // spec: RotGrid (D-Rust3: &'static, built once)
    fn rot_grid(p: Self::Piece, r: u8) -> &'static Vec<Vec<Option<Self::Piece>>>;
    // spec: InitialYX (InitialY, InitialX)
    fn initial_y(p: Self::Piece) -> i64;
    fn initial_x(p: Self::Piece) -> i64;
}

// ── PieceOrExtra: mg's cell content ──────────────────────────────────────

/// No `T1.v` counterpart: `Grid.L` tracks occupancy only, never cell
/// identity. `Piece` is the real, currently-fixed piece; `Extra` is
/// whatever a higher layer reserves instead (never constructed through T6,
/// where `CellExtra = Infallible`).
pub enum PieceOrExtra<P: Params> {
    Piece(P::Piece),
    Extra(P::CellExtra),
}

// Manual, not `#[derive(...)]`: deriving would bound each impl on `P:
// Trait` itself rather than on `P::Piece`/`P::CellExtra`, wrong here since
// `P` is a zero-sized marker with no reason to be `Copy`/`Debug`/etc.
impl<P: Params> Copy for PieceOrExtra<P> {}

impl<P: Params> Clone for PieceOrExtra<P> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<P: Params> PartialEq for PieceOrExtra<P> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (PieceOrExtra::Piece(a), PieceOrExtra::Piece(b)) => a == b,
            (PieceOrExtra::Extra(a), PieceOrExtra::Extra(b)) => a == b,
            _ => false,
        }
    }
}

impl<P: Params> Eq for PieceOrExtra<P> {}

impl<P: Params> std::fmt::Debug for PieceOrExtra<P> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PieceOrExtra::Piece(p) => f.debug_tuple("Piece").field(p).finish(),
            PieceOrExtra::Extra(e) => f.debug_tuple("Extra").field(e).finish(),
        }
    }
}

// ── Cell: shared occupancy predicate for both grid representations ─────────
// spec: L, generalized over cell type (D1, D13: one shared predicate, no
// duplicated per-representation logic).
pub trait Cell: Copy {
    fn occ(self) -> bool;
}

impl Cell for bool {
    #[inline]
    fn occ(self) -> bool {
        self
    }
}

// spec: L, specialized to `Option<Piece>` grids (`mg`, `RotGrid`'s output).
impl<T: Copy> Cell for Option<T> {
    #[inline]
    fn occ(self) -> bool {
        self.is_some()
    }
}

// ── Free functions: parameter-independent grid algebra (§4's idioms) ──────
// None of these call into `Params`; generic only over the cell type(s) they
// operate on.

/// spec: IsFullLineb (row-level only; box-membership is the caller's
/// responsibility via guard-before-index, D9).
pub fn is_full_row<T>(row: &[T], occ: impl Fn(&T) -> bool) -> bool {
    row.iter().all(occ)
}

fn dims<T>(g: &[Vec<T>]) -> (i64, i64) {
    let h = g.len() as i64;
    let w = if h > 0 { g[0].len() as i64 } else { 0 };
    (h, w)
}

/// spec: `_ ∩ _ ⊈ ∅`
///
/// True iff `g1` (embedded at `(y1,x1)`) and `g2` (embedded at `(y2,x2)`)
/// share an occupied cell. Negated at call sites for the `⊆ ∅` (no overlap)
/// reading.
pub fn intersect<T1: Cell, T2: Cell>(
    g1: &[Vec<T1>],
    y1: i64,
    x1: i64,
    g2: &[Vec<T2>],
    y2: i64,
    x2: i64,
) -> bool {
    let (h2, w2) = dims(g2);
    for (dy, row) in g1.iter().enumerate() {
        for (dx, &c1) in row.iter().enumerate() {
            if !c1.occ() {
                continue;
            }
            let ay = y1 + dy as i64;
            let ax = x1 + dx as i64;
            // guard-before-index (D9): bounds conjuncts first
            if ay < y2 || ay >= y2 + h2 || ax < x2 || ax >= x2 + w2 {
                continue;
            }
            let ly = (ay - y2) as usize;
            let lx = (ax - x2) as usize;
            if g2[ly][lx].occ() {
                return true;
            }
        }
    }
    false
}

/// spec: `_ ⊆ Full _`
///
/// Every occupied cell of `g1` (embedded at `(y1,x1)`) lies inside `g2`'s
/// box (embedded at `(y2,x2)`); `g2`'s content is irrelevant (`Full` makes
/// every in-box cell occupied).
pub fn occupied_inside<T1: Cell, T2>(
    g1: &[Vec<T1>],
    y1: i64,
    x1: i64,
    g2: &[Vec<T2>],
    y2: i64,
    x2: i64,
) -> bool {
    let (h2, w2) = dims(g2);
    for (dy, row) in g1.iter().enumerate() {
        for (dx, &c1) in row.iter().enumerate() {
            if !c1.occ() {
                continue;
            }
            let ay = y1 + dy as i64;
            let ax = x1 + dx as i64;
            if ay < y2 || ay >= y2 + h2 || ax < x2 || ax >= x2 + w2 {
                return false;
            }
        }
    }
    true
}

/// spec: GridInclude
///
/// Bare `⊆` — every occupied cell of `g1` (embedded at `(y1,x1)`) is inside
/// `g2`'s box *and* occupied in `g2` (embedded at `(y2,x2)`).
pub fn fully_contained_in<T1: Cell, T2: Cell>(
    g1: &[Vec<T1>],
    y1: i64,
    x1: i64,
    g2: &[Vec<T2>],
    y2: i64,
    x2: i64,
) -> bool {
    let (h2, w2) = dims(g2);
    for (dy, row) in g1.iter().enumerate() {
        for (dx, &c1) in row.iter().enumerate() {
            if !c1.occ() {
                continue;
            }
            let ay = y1 + dy as i64;
            let ax = x1 + dx as i64;
            if ay < y2 || ay >= y2 + h2 || ax < x2 || ax >= x2 + w2 {
                return false;
            }
            let ly = (ay - y2) as usize;
            let lx = (ax - x2) as usize;
            if !g2[ly][lx].occ() {
                return false;
            }
        }
    }
    true
}

/// spec: `Full _ ⊆ Full _`
///
/// Box containment only, content of neither grid is read.
pub fn bbox_inside_bbox<T1, T2>(
    g1: &[Vec<T1>],
    y1: i64,
    x1: i64,
    g2: &[Vec<T2>],
    y2: i64,
    x2: i64,
) -> bool {
    let (h1, w1) = dims(g1);
    let (h2, w2) = dims(g2);
    y1 >= y2 && y1 + h1 <= y2 + h2 && x1 >= x2 && x1 + w1 <= x2 + w2
}

/// spec: Valid. Generic over the grid's own cell type `T: Cell` (not tied to
/// `Option<P::Piece>`) — this only ever reads occupancy via `occupied_inside`/
/// `intersect`, both already generic the same way.
pub fn valid<P: Params, T: Cell>(g: &[Vec<T>], p: P::Piece, py: i64, px: i64, pr: u8) -> bool {
    let pg = P::rot_grid(p, pr);
    occupied_inside(pg, py, px, g, 0, 0) && !intersect(pg, py, px, g, 0, 0)
}

/// spec: CanMovePiece
pub fn can_move_piece<P: Params>(dy: i64, dx: i64, s: &Machine<P>) -> bool {
    let py2 = s.py + dy; // req-piece-move-def
    let px2 = s.px + dx; // req-piece-move-def
    ((dy == 0 && dx == -1) || (dy == 0 && dx == 1) || (dy == -1 && dx == 0)) // req-piece-move-dir
        && valid::<P, _>(&s.mg, s.p, py2, px2, s.pr)
}

/// `rotate_piece`'s guard factored into a named, side-effect-free predicate
/// (`gameover` excluded, checked by the caller) — mirrors `can_move_piece`
/// above. No `T1.v` counterpart; exists so a later layer's wall-kick logic
/// (T6) can probe rotation validity without performing it.
pub fn can_rotate_piece<P: Params>(cw: bool, s: &Machine<P>) -> bool {
    let delta = if cw { -1 } else { 1 };
    let pr2 = (s.pr as i64 + delta).rem_euclid(4) as u8;
    valid::<P, _>(&s.mg, s.p, s.py, s.px, pr2)
}

// ── Machine: encapsulates T1.v's State ──────────────────────────────────────

/// spec: State
#[derive(Clone)]
pub struct Machine<P: Params> {
    pub mg: Vec<Vec<Option<PieceOrExtra<P>>>>, // spec: mg — req-piece-loc (main grid)
    pub p: P::Piece,                           // spec: p
    pub py: i64,                               // spec: py — req-piece-loc
    pub px: i64,                               // spec: px — req-piece-loc
    pub pr: u8,                                // spec: pr
    pub gameover: bool,                        // spec: gameover — req-flow
    pub cleared_lines: i64,                    // spec: clearedLines
}

impl<P: Params> Machine<P> {
    /// spec: Init. `check_axioms::<P>()` is not called here — axioms
    /// constrain parameters, not state, checked once by the caller before
    /// the first `Machine<P>` of a given `P` is constructed.
    ///
    /// `piece_source` supplies a piece for each occupied cell of
    /// `P::initial_main_grid()` (D1's `bool`→`Option<Piece>` widening has no
    /// canonical filler); never called when `InitialMainGrid` is all-`false`.
    /// Which piece it picks is never read by engine logic, only cosmetic to
    /// rendering.
    pub fn new(p: P::Piece, mut piece_source: impl FnMut() -> P::Piece) -> Self {
        let mg: Vec<Vec<Option<PieceOrExtra<P>>>> = P::initial_main_grid()
            .iter()
            .map(|row| {
                row.iter()
                    .map(|&occupied| {
                        if occupied {
                            Some(PieceOrExtra::Piece(piece_source()))
                        } else {
                            None
                        }
                    })
                    .collect()
            })
            .collect();
        let py = P::initial_y(p); // req-piece-init
        let px = P::initial_x(p); // req-piece-init
        let gameover = intersect(P::forbidden_grid(), P::FY, P::FX, &mg, 0, 0);
        let m = Machine {
            mg,
            p,
            py,
            px,
            pr: 0,
            gameover,
            cleared_lines: 0,
        };
        if CHECK_INVARIANTS {
            check_invariants(&m);
        }
        m
    }

    /// spec: MovePiece
    pub fn move_piece(&mut self, dy: i64, dx: i64) -> bool {
        if self.gameover || !can_move_piece(dy, dx, self) {
            // req-flow, req-piece-move-dir
            return false;
        }
        self.py += dy; // req-piece-move-def
        self.px += dx; // req-piece-move-def
        if CHECK_INVARIANTS {
            check_invariants(self);
        }
        true
    }

    /// spec: RotatePiece
    pub fn rotate_piece(&mut self, cw: bool) -> bool {
        let delta = if cw { -1 } else { 1 };
        let pr2 = (self.pr as i64 + delta).rem_euclid(4) as u8; // req-piece-rot, D4
        if self.gameover || !valid::<P, _>(&self.mg, self.p, self.py, self.px, pr2) {
            // req-flow
            return false;
        }
        self.pr = pr2;
        if CHECK_INVARIANTS {
            check_invariants(self);
        }
        true
    }

    /// spec: `(mg s ∪ (PieceGrid s ⊕ pyx s)) ∩ Full (mg s)`, fused (D13):
    /// overlay the current piece directly onto `self.mg`, O(PW²), never a
    /// fresh HM×WM grid.
    fn overlay_piece(&mut self) {
        let pg = P::rot_grid(self.p, self.pr);
        for dy in 0..P::PW {
            for dx in 0..P::PW {
                if let Some(piece) = pg[dy as usize][dx as usize] {
                    let (gy, gx) = (self.py + dy, self.px + dx);
                    if gy >= 0 && gx >= 0 {
                        let (gy, gx) = (gy as usize, gx as usize);
                        if gy < self.mg.len() && gx < self.mg[0].len() {
                            self.mg[gy][gx] = Some(PieceOrExtra::Piece(piece));
                        }
                    }
                }
            }
        }
    }

    /// spec: FixPiece. `GridUnion`/`ClearFullLines`/`FullLineCount` realized
    /// in place (D13, D2) — `mg` is uniquely owned, nothing aliases its
    /// pre-overlay contents past this call.
    pub fn fix_piece(&mut self, p_new: P::Piece) -> bool {
        if self.gameover || can_move_piece(-1, 0, self) {
            // req-flow
            return false;
        }
        if CHECK_INVARIANTS {
            assert!(P::piece_all().contains(&p_new)); // D5
        }

        self.overlay_piece(); // spec: u — GridUnion, fused

        // spec: FullLineCount, fused: count on the overlaid grid.
        self.cleared_lines = self // req-grid-clear
            .mg
            .iter()
            .filter(|row| is_full_row(row, Option::is_some))
            .count() as i64;

        // spec: ClearFullLines, fused: swap-partition, no drop/alloc; order preserved.
        let mut write = 0;
        for read in 0..self.mg.len() {
            if !is_full_row(&self.mg[read], Option::is_some) {
                if write != read {
                    self.mg.swap(write, read);
                }
                write += 1;
            }
        }
        for row in &mut self.mg[write..] {
            row.fill(None);
        }

        self.p = p_new; // req-piece-fix-new
        self.py = P::initial_y(p_new); // req-piece-fix-new
        self.px = P::initial_x(p_new); // req-piece-fix-new
        self.pr = 0; // req-piece-fix-new
        self.gameover = intersect(P::forbidden_grid(), P::FY, P::FX, &self.mg, 0, 0); // req-piece-fix-gameover

        if CHECK_INVARIANTS {
            check_invariants(self);
        }
        true
    }

    /// spec: FallStep (disjoint-guard sequencing: exactly one of
    /// `move_piece`/`fix_piece` fires whenever `!self.gameover`).
    pub fn fall_step(&mut self, p_new: P::Piece) -> bool {
        if self.move_piece(-1, 0) {
            return true; // req-piece-fall
        }
        self.fix_piece(p_new) // req-piece-fix
    }
}

// ── Axiom/invariants checker ────────────────────────────────────────────────

/// spec: the `Axioms*` blocks (minus `Contained` conjuncts, D-Contained,
/// and D8's finiteness/disjointness conjuncts), plus D10's headroom bound.
/// Called once per `P`, before any `Machine<P>` is constructed.
pub fn check_axioms<P: Params>() {
    // AxiomsPW
    assert!(P::PW > 0, "AxiomsPW: PW must be > 0, got {}", P::PW);

    let (hm, wm) = dims(P::initial_main_grid());

    // AxiomsInitialYX
    for &p in P::piece_all() {
        let iy = P::initial_y(p);
        let ix = P::initial_x(p);
        assert!(
            1 - P::PW <= iy && iy < hm,
            "AxiomsInitialYX: {p:?}'s initial_y={iy} outside [{}, {hm})",
            1 - P::PW
        );
        assert!(
            1 - P::PW <= ix && ix < wm,
            "AxiomsInitialYX: {p:?}'s initial_x={ix} outside [{}, {wm})",
            1 - P::PW
        );
    }

    // AxiomsRotGrid
    for &p in P::piece_all() {
        for r in 0..4u8 {
            let g = P::rot_grid(p, r);
            assert!(
                g.len() as i64 == P::PW,
                "AxiomsRotGrid: {p:?} r{r} has height {}, expected PW={}",
                g.len(),
                P::PW
            );
            assert!(
                g.iter().all(|row| row.len() as i64 == P::PW),
                "AxiomsRotGrid: {p:?} r{r} has a row whose width isn't PW={}",
                P::PW
            );
            assert!(
                g.iter().flatten().any(|c| c.is_some()),
                "AxiomsRotGrid: {p:?} r{r} has no occupied cell"
            );
        }
        let g0 = P::rot_grid(p, 0);
        assert!(
            fully_contained_in(
                g0,
                P::initial_y(p),
                P::initial_x(p),
                P::forbidden_grid(),
                P::FY,
                P::FX
            ),
            "AxiomsRotGrid: {p:?}'s r0 grid at spawn (initial_y={}, initial_x={}) isn't fully \
             contained in ForbiddenGrid at (FY={}, FX={})",
            P::initial_y(p),
            P::initial_x(p),
            P::FY,
            P::FX
        );
    }

    // AxiomsInitialMainGrid (minus Contained)
    assert!(
        hm > 0,
        "AxiomsInitialMainGrid: height must be > 0, got {hm}"
    );
    assert!(wm > 0, "AxiomsInitialMainGrid: width must be > 0, got {wm}");
    for (y, row) in P::initial_main_grid().iter().enumerate() {
        assert!(
            !is_full_row(row, |&b: &bool| b),
            "AxiomsInitialMainGrid: row {y} is already a full line"
        );
    }

    // AxiomsForbiddenGrid (minus Contained)
    let (fh, fw) = dims(P::forbidden_grid());
    assert!(fh > 0, "AxiomsForbiddenGrid: height must be > 0, got {fh}");
    assert!(fw > 0, "AxiomsForbiddenGrid: width must be > 0, got {fw}");
    assert!(
        bbox_inside_bbox(
            P::forbidden_grid(),
            P::FY,
            P::FX,
            P::initial_main_grid(),
            0,
            0
        ),
        "AxiomsForbiddenGrid: ForbiddenGrid's box at (FY={}, FX={}), {fh}x{fw}, isn't inside \
         InitialMainGrid's box at (0,0), {hm}x{wm}",
        P::FY,
        P::FX
    );

    // D10: overflow-safe headroom check — this form never adds two
    // possibly-large values, so it can't itself overflow.
    assert!(
        std::cmp::max(hm, wm) <= i64::MAX - P::PW + 1,
        "D10: max(HM={hm}, WM={wm}) + PW({}) - 1 would overflow i64",
        P::PW
    );
}

/// spec: TypeOK
pub fn type_ok<P: Params>(s: &Machine<P>) -> bool {
    let (hm, wm) = dims(P::initial_main_grid());
    s.mg.len() as i64 == hm
        && s.mg.iter().all(|row| row.len() as i64 == wm)
        && s.mg.iter().flatten().all(|c| match c {
            None => true,
            Some(PieceOrExtra::Piece(p)) => P::piece_all().contains(p),
            Some(PieceOrExtra::Extra(_)) => true, // reserved for a higher layer — always valid here
        })
        && s.pr < 4
        && P::piece_all().contains(&s.p)
}

/// spec: Correct (D7). Every conjunct uses `assert!`, not `debug_assert!`
/// — the latter compiles to nothing under `--release`, which would defeat
/// D7's independence from build profile. Mirrors `Correct`'s five
/// conjuncts, calling `type_ok` rather than re-implementing it.
pub fn check_invariants<P: Params>(s: &Machine<P>) {
    // TypeOK
    assert!(type_ok(s));

    let pg = P::rot_grid(s.p, s.pr);

    // PieceOccupiedInsideBounds
    assert!(occupied_inside(pg, s.py, s.px, &s.mg, 0, 0));

    // PieceOnFreeBlocks — req-piece-free
    if !s.gameover {
        assert!(!intersect(pg, s.py, s.px, &s.mg, 0, 0));
    }

    // NoFullLine
    assert!(!s.mg.iter().any(|row| is_full_row(row, Option::is_some)));

    // Gameover
    assert!(s.gameover == intersect(P::forbidden_grid(), P::FY, P::FX, &s.mg, 0, 0));
}

// ── Helpers for refining models ─────────────────────────────────────────────
//
// No call site in `T1.v`'s own `Next`, but still real `Definition`s the
// coverage check requires translating. Unlike the guarded transitions
// above, these three are total, so they mutate `s` in place and return
// nothing rather than a fresh state value.

/// spec: NewPieceState
pub fn new_piece_state<P: Params>(p_new: P::Piece, s: &mut Machine<P>) {
    s.p = p_new;
    s.py = P::initial_y(p_new);
    s.px = P::initial_x(p_new);
    s.pr = 0;
    // mg, gameover, cleared_lines unchanged
}

/// spec: NewPieceYXState
pub fn new_piece_yx_state<P: Params>(py_new: i64, px_new: i64, s: &mut Machine<P>) {
    s.py = py_new;
    s.px = px_new;
    // mg, p, pr, gameover, cleared_lines unchanged
}

/// spec: NewMainGridGameoverState
pub fn new_main_grid_gameover_state<P: Params>(
    mg: Vec<Vec<Option<PieceOrExtra<P>>>>,
    gameover: bool,
    s: &mut Machine<P>,
) {
    s.mg = mg;
    s.gameover = gameover;
    // p, pyx, pr, cleared_lines unchanged
}
