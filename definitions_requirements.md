Note: Definitions have identifiers of the form 'def-*'. Requirements have
    identifiers of the form 'req-*'.

req-flow: The game is either running or over (game over).

Note: In the following, all requirements assume the game is running, except when
explicitly stated otherwise.

def-grid: A grid is a boolean-valued 2D matrix.

def-block: A block exists at a coordinate in a grid.

def-block-occupied: A block is occupied in a grid iff its corresponding
    boolean value is True.

def-block-free: A block is free in a grid iff it is not occupied.

def-grid-main: The main grid is where the pieces "live" (move, fix, see below).

def-piece: A piece has its own grid, a position in the main grid and a rotation
    angle.

def-piece-type: There are several piece types, each having its specific grid.

req-piece-ctrl: At any time, exactly one piece is controlled by the player.

def-grid-sub: A sub-grid is a grid included in another grid.

Note: In the following, we may use the word "piece" instead of the longer but
    more correct expression "piece's grid". The reader is expected to
    understand based on the context.

def-grid-intersection: Given two grids and their positions in an absolute
    coordinate system, their intersection is a located grid where a block is
    occupied iff the corresponding blocks in both grids are occupied.

def-grid-forbidden: A forbidden grid is a sub-grid of the main grid where the
    current piece is not allowed to fix.

def-piece-current: The piece currently controlled by the player.

req-piece-loc: The current piece is fully included inside the main grid.

req-piece-free: The current piece does not intersect with the main grid (i.e.
    their intersection is empty).

req-piece-init: When the current piece appears, it is included in the forbidden
    grid.

req-piece-move-dir: The player can move the current piece towards left,
    right or bottom, iff the resulting piece does not intersect the main grid.

req-piece-move-def: Moving a piece in a direction translates the piece by one
    block in the main grid along the said direction.

req-piece-rot: The player can rotate a piece, either clockwise or
    counter-clockwise, iff the resulting piece does not intersect the main grid.

req-piece-fall: Periodically, the current piece tries to move by itself towards
    bottom.

def-piece-fix: A fixed piece cannot move anymore.

req-piece-fix: If the current piece cannot move towards bottom, it fixes.

req-piece-fix-gameover: If the current piece fixes and intersects the forbidden
    grid, the game is over.

Note: For the game to be playable, the forbidden grid is expected to allow
    the initial current piece to move out of it.

req-piece-fix-new: If the current piece fixes and does not cause a game over, a
    new current piece is chosen.

def-line: A line is a row in the grid.

def-line-clear: Clearing a line is making it disappear and shifting any line
    above towards bottom by one block.

req-grid-clear: When the current piece fixes, any full line is cleared.

def-grid-empty: A grid is empty iff all its blocks are free.

req-grid-init: Initially, the grid has no full line.

def-piece-drop: Dropping a piece instantly is moving it to its lowest possible
    position and fixing it (it is equivalent to move it towards bottom until it
    fixes).

req-piece-drop: The player can drop the current piece.

def-piece-shadow: The shadow of a piece is the piece to its lowest possible
    location (i.e. where it would drop).

req-piece-shadow: The current piece has a shadow.

req-score: Clearing lines raises the player score.

def-clearing: Disappearance of some full lines and shifting of above lines after
    the current piece has fixed.

def-combo: Number of consecutive clearings minus 1, i.e. first clearing is
    0-combo, next consecutive clearing is 1-combo, etc.

def-perfect-clear: Clearing that leaves the main grid empty.

req-score-formula: When a clearing occurs, the score is raised by the formula
    LineClearPoints + ComboPoints + PerfectClearPoints where:
    - LineClearPoints = 
        CASE clearedLines = 1 -> 100 * level
        CASE clearedLines = 2 -> 300 * level
        CASE clearedLines = 3 -> 500 * level
        CASE clearedLines = 4 -> 800 * level
        CASE OTHER            -> 800 * level
    - ComboPoints =
        IF combo > 0 THEN (50 * combo * level) ELSE 0
    - PerfectClearPoints = 
        IF NOT perfectClear
        THEN 0
        ELSE CASE clearedLines = 1 ->  800 * level
             CASE clearedLines = 2 -> 1200 * level
             CASE clearedLines = 3 -> 1800 * level
             CASE clearedLines = 4 -> 2000 * level
             CASE OTHER            -> 2000 * level

req-score-init: Initially, the score is 0.

req-level: The greater the level, the faster the current piece falls.

req-level-formula: The level raises by one every ten cleared lines.

req-level-init: Initially, the level is 1.

def-hold-slot: A slot separated from the main grid that can contain a piece.

def-hold-piece: Holding a piece is putting it in the hold slot.

req-hold: The player can hold the current piece.

req-hold-swap: When holding the current piece, if the hold slot is not empty
    the held piece becomes the current piece.

req-hold-empty: When holding the current piece, if the hold slot is empty, a new
    piece becomes the current piece in the same way that happens after the
    current piece has fixed.

req-hold-limit: Once the current piece has been held, holding is not
    possible until the new current piece is fixed.

def-preview: The piece preview (or preview for short) is a sequence of
    next pieces, i.e. pieces that will become current pieces.

req-preview-len: The preview length is constant.

def-preview-bag: The preview bag is the set of available pieces for preview
    population.

def-preview-bag-init: Initially, the preview bag is the set of all piece types.

req-preview-init: The preview is populated by randomly picking and removing
    pieces, one at a time, from the preview bag. When the bag is empty, it is
    restored to its initial value. This process stops when the preview is full.

def-pop: Popping a non-empty sequence is removing its first element and shifting
    subsequent element (the second becomes the first, and so on).

req-preview-pop: When a new current piece is needed, it is popped from the
    preview. The new last piece is picked from the bag in the same manner as
    initial preview population.

req-piece-kick: When the current piece rotation is impossible, the piece is moved to the
    left by one if it makes the rotation possible. If the rotation is still
    impossible, the piece is moved to the right by one, with respect to its original
    position, if it makes the rotation possible.

Note: req-piece-kick is an extension of what req-piece-rot allows.

req-multi: The game can be simultaneously played by more than one player.

def-one-hole-line: A one-hole line is a line containing exactly one free block.

def-multi-garbage: Garbage consists of one-hole lines, generated when a player
    clears lines, and sent to another player.

def-multi-garbage-pending: The garbage a player has received but that has not
    yet materialized on her main grid.

def-multi-target: The player the garbage is sent to.

def-multi-winner: The last player whose game is not over is the winner.

req-multi-target-nonself: A player is never her own target, except when it is
    the winner.

req-multi-succ: Each player has a successor.

req-multi-garbage-gen: When a player clears lines, the generated garbage is
    computed, in number of lines, by the formula
    NormalGarbage + SpecialGarbage where (with c = clearedLines):
    - NormalGarbage = max(IF c < 4 THEN c - 1 ELSE c, 0)
    - SpecialGarbage = IF perfectClear THEN 10 ELSE 0

req-multi-garbage-cancel: Once a player has generated garbage, this
    garbage cancels her received pending garbage: generated garbage is consumed
    by being subtracted from the pending garbage.

req-multi-garbage-send: Once pending garbage has been canceled, the remaining
    generated garbage, if any, is sent to the target (or its first successor
    that is not gameover), and the target becomes its first successor that is
    not game over.

req-multi-garbage-materialize: After a player has fixed her current piece and
    pending-garbage cancellation has been applied, the remaining pending
    garbage, if any, is consumed by materializing as one-hole lines appearing at
    the bottom of her main grid. Existing occupied blocks are pushed upward
    accordingly.

req-multi-gameover: The single-player gameover condition (see
    req-piece-fix-gameover) is extended with the following: the game is over for
    a given player if occupied blocks would occupy a row above the top row of
    her main grid. This can happen after garbage has materialized and existing
    occupied blocks have been pushed above the top of the main grid.
