export * from '../../t3/tests/testInstance.js';

// req-preview-len: NextLen for the small fixture — deliberately short (crosses a
// bag boundary quickly, MaxBagLen == Piece.length == 2 for this fixture) so unit
// tests can hand-verify exact bag_/next_ sequences (see model.unit.test.js).
export const NextLen = 3;
