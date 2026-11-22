import AFTD.Prelude
import AFTD.Kb.Physics.ThermomajorizationWitnessY
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# thermomajorization_witness_y_mem_antitone_stdSimplex

Topic: quantum_mechanics   Node: cf13f71e2bea

Provenance: helper lemma. OP-2138

For any dimension n and rank 0 < j ≤ n, the thermomajorization candidate vector witness_y n j is a nonincreasing probability vector in the standard simplex.
-/

/-- Thermomajorization witness vector y is a nonincreasing probability vector. -/
theorem thermomajorization_witness_y_mem_antitone_stdSimplex (n j : ℕ)
    (hj0 : 0 < j) (hjn : j ≤ n) :
    thermomajorization_witness_y n j ∈ stdSimplex ℝ (Fin n) ∧
      Antitone (thermomajorization_witness_y n j) := by
  have h_nonneg : ∀ i, 0 ≤ thermomajorization_witness_y n j i := by
    intro i
    simp only [thermomajorization_witness_y]
    split_ifs with h
    · positivity
    · exact le_refl 0
  have hsum : ∑ i : Fin n, thermomajorization_witness_y n j i = 1 := by
    simp only [thermomajorization_witness_y]
    rw [Fin.sum_univ_eq_sum_range (fun k => if k < j then (1 : ℝ) / j else 0) n]
    rw [← Finset.sum_filter]
    have hfilter : (Finset.range n).filter (fun k => k < j) = Finset.range j := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [hfilter, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  refine ⟨⟨h_nonneg, hsum⟩, ?_⟩
  intro i i' hii
  by_cases h1 : (i' : ℕ) < j
  · have h2 : (i : ℕ) < j := lt_of_le_of_lt hii h1
    simp [thermomajorization_witness_y, h1, h2]
  · have h0 : thermomajorization_witness_y n j i' = 0 := by
      simp [thermomajorization_witness_y, h1]
    rw [h0, thermomajorization_witness_y]
    split_ifs with h2
    · positivity
    · exact le_refl 0
