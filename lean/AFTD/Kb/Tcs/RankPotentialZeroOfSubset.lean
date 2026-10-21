import AFTD.Prelude
import AFTD.Kb.Tcs.FifoQueue
import AFTD.Kb.Tcs.FifoRank
import AFTD.Kb.Tcs.RankPotential

/-!
# rank_potential_zero_of_subset

Topic: online_algorithms   Node: 7f13c77779f9

Provenance: helper lemma. arXiv:2610.18767 Section 3.2, line 414

If all pages in the online FIFO cache are present in the offline cache, the rank potential Φ is zero; in particular, the initial potential Φ₀ = 0.
-/

/-- Rank potential is zero when online cache is a subset of offline cache. -/
theorem rank_potential_zero_of_subset {α : Type*} [DecidableEq α] {k : ℕ} (q : FifoQueue α k) (cOpt : Finset α) (h : q.pages.toFinset ⊆ cOpt) : rank_potential q cOpt = 0 := by
  unfold rank_potential
  rw [Finset.sdiff_eq_empty_iff_subset.mpr h, Finset.sum_empty]
