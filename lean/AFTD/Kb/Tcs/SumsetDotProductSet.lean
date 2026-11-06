import AFTD.Prelude
import AFTD.Kb.Tcs.SumsetSumVectorsFinset
import AFTD.Kb.Tcs.SumsetFinsetSortedVector
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# sumset_dot_product_set

Topic: combinatorics   Node: 4379d9d7597d

Provenance: formalization of a published result. Source: arXiv:2611.07303 Proposition 5.7

For natural numbers h, k, and q, sumset_dot_product_set h k q is the finset of all values dotProduct x (sumset_finset_sorted_vector k A) where x ∈ sumset_sum_vectors_finset (h + 1) k and A is a k-element subset of {1, ..., q}.
-/

/-- The set S_{h+1,k}(q) of all dot products x · vec(A) for x ∈ X_{h+1,k} and A ∈ binom([q], k). -/
def sumset_dot_product_set (h k : ℕ) (q : ℕ) : Finset ℤ := ((sumset_sum_vectors_finset (h + 1) k) ×ˢ ((Finset.Icc 1 (q : ℤ)).powersetCard k)).image fun (x, A) => dotProduct x (sumset_finset_sorted_vector k A)
