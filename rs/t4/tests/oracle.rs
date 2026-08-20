// spec: tests/oracle.rs — executable T4.v reference (§9, `implementation.md`).
//
// §0.1: only T4's own bag/next mechanics are re-tested here; `s3` (wrapped
// `t3::model::Machine`) is not. §9: `OracleDraw` is deliberately
// differently-shaped from `model.rs`'s `draw_once`/`init_piece_and_draw`,
// so a shared bug would have to be conceptual, not copy-paste.

#![allow(dead_code)]

/// Oracle state for bag/next mechanics only — index-based, sharing no code
/// shape with `model.rs` (§9).
pub struct OracleDraw<T: Copy + PartialEq> {
    pub bag: Vec<T>,  // logically bag_ 0..bag.len(), popped from the end
    pub next: Vec<T>, // logically next_ 0..NEXT_LEN, next[0] is "next s 0"
}

impl<T: Copy + PartialEq> OracleDraw<T> {
    /// spec: DrawNextPiece, reimplemented independently — index-remove from
    /// the front of `next` (`Vec::remove(0)`; not performance-sensitive)
    /// and index-pop the bag's last element, mirroring `bag_ (bagLen_-1)`.
    pub fn draw_once(&mut self, bag_new: &[T]) -> (T, bool) {
        let resetting = self.bag.len() == 1;
        let p = self.next.remove(0);
        let popped = self.bag.remove(self.bag.len() - 1);
        self.next.push(popped);
        if resetting {
            self.bag = bag_new.to_vec();
        }
        (p, resetting)
    }
}

/// spec: BuildInitNext + InitPieceAndDraw, reimplemented independently —
/// same algorithm, different data structure and control-flow shape from
/// `model.rs`'s `init_piece_and_draw` (§9).
pub fn oracle_init_piece_and_draw<T: Copy + PartialEq>(
    next_len: usize,
    mut bags_fn: impl FnMut(u64) -> Vec<T>,
) -> (T, OracleDraw<T>) {
    let mut d = OracleDraw {
        bag: bags_fn(0),
        next: vec![bags_fn(0)[0]; next_len],
    };
    let mut bag_idx: u64 = 1;
    let mut k = 0usize;
    while k < next_len {
        let (_, resetting) = d.draw_once(&bags_fn(bag_idx));
        if resetting {
            bag_idx += 1;
        }
        k += 1;
    }
    let (p, _) = d.draw_once(&bags_fn(bag_idx));
    (p, d)
}
