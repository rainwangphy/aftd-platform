import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixRankAddLe

/-!
# Matrix.rank_sum_le

Topic: communication   Node: c8d235940116

Provenance: helper lemma. TCSlib, `Matrix.rank_sum_le`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/Rank.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Subadditivity of matrix rank over finite sums. Let $s$ be a finite subset of an index set, and let $(A_i)_{i \in s}$ be a family of
real matrices with rows indexed by a set $X$ and columns indexed by a finite set $Y$.
Then the rank of their sum is at most the sum of their ranks:
\[
\mathrm{rank}\!\left(\sum_{i \in s} A_i\right) \;\le\; \sum_{i \in s}
\mathrm{rank}(A_i).
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- Matrix rank is subadditive over finite sums: the rank of `∑ i ∈ s, A i` is at most `∑ i ∈ s, rank (A i)` [RY20, Fact 2.3], iterated. Stated for real matrices only; candidate for upstreaming to Mathlib. -/
theorem Matrix.rank_sum_le {X Y : Type*} [Fintype Y]
    {ι : Type*} (s : Finset ι) (A : ι → Matrix X Y ℝ) :
    (∑ i ∈ s, A i).rank ≤ ∑ i ∈ s, (A i).rank := by
  classical
  induction s using Finset.induction with
  | empty => simp [Matrix.rank_zero]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (Matrix.rank_add_le _ _).trans (Nat.add_le_add_left ih _)
