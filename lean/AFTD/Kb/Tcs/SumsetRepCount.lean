import AFTD.Prelude
import AFTD.Kb.Tcs.SumsetSumVectorsFinset
import AFTD.Kb.Tcs.SumsetFinsetSortedVector
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# sumset_rep_count

Topic: combinatorics   Node: 23ca2a76325d

Provenance: formalization of a published result. Source: arXiv:2611.07303 Proposition 5.7

For natural numbers h, k, q and integer s, sumset_rep_count h k q s is the number of pairs (x, A) in (sumset_sum_vectors_finset (h + 1) k) × (Finset.Icc 1 (q : ℤ)).powersetCard k such that dotProduct x (sumset_finset_sorted_vector k A) = s.
-/

/-- The representation count ν_q(s) of s as a dot product x · vec(A) for x ∈ X_{h+1,k} and A ∈ binom([q], k). -/
def sumset_rep_count (h k : ℕ) (q : ℕ) (s : ℤ) : ℕ := (((sumset_sum_vectors_finset (h + 1) k) ×ˢ ((Finset.Icc 1 (q : ℤ)).powersetCard k)).filter fun (x, A) => dotProduct x (sumset_finset_sorted_vector k A) = s).card
