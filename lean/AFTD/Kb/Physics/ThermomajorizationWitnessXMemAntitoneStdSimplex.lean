import AFTD.Prelude
import AFTD.Kb.Physics.ThermomajorizationWitnessX
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Physics.ThermomajorizationPointwiseMissedErrorGeGapError

/-!
# thermomajorization_witness_x_mem_antitone_stdSimplex

Topic: quantum_mechanics   Node: 3ad9a6435a4c

Provenance: helper lemma. OP-2138

For any dimension n and integers a < j < b ≤ n, the thermomajorization candidate vector witness_x n a j b is a nonincreasing probability vector in the standard simplex.
-/

lemma thermomajorization_witness_x_mem_antitone_stdSimplex_sum_ite_lt (n k : ℕ) (hk : k ≤ n) (d : ℝ) :
    (∑ x : Fin n, (if (x : ℕ) < k then d else 0)) = (k : ℝ) * d := by
  rw [← Finset.sum_filter]
  have hcard : (Finset.filter (fun x : Fin n => (x : ℕ) < k) Finset.univ).card = k :=
    thermomajorization_pointwise_missed_error_ge_gap_error_card_fin_filter_lt n k hk
  rw [Finset.sum_const, hcard, nsmul_eq_mul]

lemma thermomajorization_witness_x_mem_antitone_stdSimplex_antitone_ite_lt (n k : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    Antitone (fun (i : Fin n) => if (i : ℕ) < k then c else 0) := by
  intro x y hxy
  dsimp
  split_ifs with h1 h2 h3
  · exact le_rfl
  · exfalso
    have hxy_nat : (x : ℕ) ≤ (y : ℕ) := Fin.le_def.mp hxy
    exact h2 (lt_of_le_of_lt hxy_nat h1)
  · exact hc
  · exact le_rfl

/-- Thermomajorization witness vector x is a nonincreasing probability vector. -/
theorem thermomajorization_witness_x_mem_antitone_stdSimplex (n a j b : ℕ)
    (ha : a < j) (hj : j < b) (hb : b ≤ n) :
    thermomajorization_witness_x n a j b ∈ stdSimplex ℝ (Fin n) ∧
      Antitone (thermomajorization_witness_x n a j b) := by
  have haR : (a : ℝ) < (j : ℝ) := Nat.cast_lt.mpr ha
  have hjR : (j : ℝ) < (b : ℝ) := Nat.cast_lt.mpr hj
  have hj0 : (0 : ℝ) < (j : ℝ) := by linarith
  have hbj : 0 < (b : ℝ) - (j : ℝ) := by linarith
  have hba : 0 < (b : ℝ) - (a : ℝ) := by linarith
  have hd1 : 0 ≤ ((b : ℝ) - (j : ℝ)) / ((j : ℝ) * ((b : ℝ) - (a : ℝ))) := by positivity
  have hd2 : 0 ≤ ((j : ℝ) - (a : ℝ)) / ((j : ℝ) * ((b : ℝ) - (a : ℝ))) := by positivity
  have ha_le_n : a ≤ n := by linarith
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i
    dsimp [thermomajorization_witness_x]
    split_ifs with h1 h2
    · positivity
    · positivity
    · positivity
    · positivity
  · dsimp [thermomajorization_witness_x]
    rw [Finset.sum_add_distrib]
    rw [thermomajorization_witness_x_mem_antitone_stdSimplex_sum_ite_lt n a ha_le_n]
    rw [thermomajorization_witness_x_mem_antitone_stdSimplex_sum_ite_lt n b hb]
    have hj_ne : (j : ℝ) ≠ 0 := ne_of_gt hj0
    have hba_ne : (b : ℝ) - (a : ℝ) ≠ 0 := ne_of_gt hba
    have hd_ne : (j : ℝ) * ((b : ℝ) - (a : ℝ)) ≠ 0 := mul_ne_zero hj_ne hba_ne
    field_simp
    ring
  · dsimp [thermomajorization_witness_x]
    exact Antitone.add
      (thermomajorization_witness_x_mem_antitone_stdSimplex_antitone_ite_lt n a _ hd1)
      (thermomajorization_witness_x_mem_antitone_stdSimplex_antitone_ite_lt n b _ hd2)
