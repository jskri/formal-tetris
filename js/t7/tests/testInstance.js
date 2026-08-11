export * from '../../t6/tests/testInstance.js';

// T7-specific: a small multiplayer roster on top of T6's tiny (2-piece)
// physics fixture. 3 players is enough to exercise round-robin retargeting
// (req-multi-garbage-send's redirect case needs >= 3 to be non-degenerate)
// without the state-space blowup of a larger roster.
export const Player = [0, 1, 2];
export const HostIndex = 0;
