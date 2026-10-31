import AFTD.Prelude
import AFTD.Kb.Tcs.AvgPairwiseHammingDist

/-!
# avg_pairwise_hamming_dist_singleton

Topic: combinatorics   Node: 56bd619f471d

Provenance: helper lemma. folklore

For any natural number $n$ and any point $c : \mathrm{Fin}\ n \to \mathrm{Bool}$, the average pairwise Hamming distance of the singleton set $\{c\} \subseteq (\mathrm{Fin}\ n \to \mathrm{Bool})$ is $0$.
-/

/-- The average pairwise Hamming distance of a singleton in the Boolean hypercube is zero. -/
theorem avg_pairwise_hamming_dist_singleton {n : ℕ} (c : Fin n → Bool) :
    avg_pairwise_hamming_dist ({c} : Finset (Fin n → Bool)) = 0 := by
  simp [avg_pairwise_hamming_dist, hammingDist_self]
