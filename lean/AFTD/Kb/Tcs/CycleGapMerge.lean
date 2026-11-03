import AFTD.Prelude

/-!
# cycle_gap_merge

Topic: online_algorithms   Node: 671e7a7a860b

Provenance: formalization of a published result. Source: arXiv:2610.15776, Section 4 and Corollary 18

Merges the adjacent gaps at cyclic index `i` of a gap list `g` representing distances between free facilities on a cycle, combining gaps `(i - 1) % g.length` and `i` when `g.length > 1`.
-/

/-- Merges adjacent gaps at cyclic index i upon consuming the intervening facility. -/
def cycle_gap_merge (g : List ℕ) (i : ℕ) : List ℕ := let k := g.length
  if k ≤ 1 then g
  else
    let idx := i % k
    if idx = 0 then
      (g.tail.dropLast) ++ [(g.getLast?.getD 0) + (g.head?.getD 0)]
    else
      g.take (idx - 1) ++ ((g[idx - 1]?.getD 0) + (g[idx]?.getD 0)) :: g.drop (idx + 1)
