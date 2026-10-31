import AFTD.Prelude
import AFTD.Kb.Optimization.GreedyVectorChainSaturation

/-!
# greedy_vector_sum_univ

Topic: submodular   Node: 03d494ef5ec6

Provenance: helper lemma. folklore

For any set function C on Finset (Fin n) with C ∅ = 0 and any permutation π of Fin n, the sum over all i of the greedy marginal differences C(S_{rank(i)}) - C(S_{rank(i)+1}) equals C Finset.univ, where S_k is the upper set (Finset.univ.filter (fun j : Fin n => k ≤ (j : ℕ))).map π.toEmbedding.
-/

/-- The total sum of greedy marginal differences along a permutation equals the capacity of the universal set. -/
lemma greedy_vector_sum_univ {n : ℕ} (C : Finset (Fin n) → ℝ)
    (hC_empty : C ∅ = 0) (π : Equiv.Perm (Fin n)) :
    ∑ i, (C ((Finset.univ.filter (fun j : Fin n => (π.symm i : ℕ) ≤ (j : ℕ))).map π.toEmbedding) -
          C ((Finset.univ.filter (fun j : Fin n => (π.symm i : ℕ) + 1 ≤ (j : ℕ))).map π.toEmbedding)) =
      C Finset.univ := by
  have h0 : (Finset.univ.filter (fun j : Fin n => 0 ≤ (j : ℕ))).map π.toEmbedding = Finset.univ := by
    have hfilt : (Finset.univ.filter (fun j : Fin n => 0 ≤ (j : ℕ))) = Finset.univ := by
      ext j
      simp
    rw [hfilt]
    ext x
    simp
  have hsat := greedy_vector_chain_saturation C hC_empty π 0 (Nat.zero_le n)
  rw [h0] at hsat
  exact hsat
