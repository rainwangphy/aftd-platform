import AFTD.Prelude
import AFTD.Kb.Physics.HypergraphBinomialDeficit
import AFTD.Kb.Physics.HypergraphDeficitH

/-!
# op_1668_hypergraph_binomial_deficit_pos

Topic: quantum_mechanics   Node: 8779700896ae

Provenance: original. Related work: arXiv:2610.42129; OP-1668

For every natural number n ≥ 3 and every real number p with 0 < p < 1/2, the hypergraph binomial deficit hypergraph_binomial_deficit n p is strictly positive.
-/

lemma op_1668_hypergraph_binomial_deficit_pos_aux_pos (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (j : ℕ) :
    0 < hypergraph_deficit_h p j := by
  unfold hypergraph_deficit_h
  exact div_pos (mul_pos (mul_pos (by norm_num) (pow_pos hp0 j)) (pow_pos (by linarith) j))
    (pow_pos (add_pos (pow_pos hp0 j) (pow_pos (by linarith) j)) 2)

lemma op_1668_hypergraph_binomial_deficit_pos_aux_nonneg (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (j : ℕ) :
    0 ≤ hypergraph_deficit_h p j := by
  unfold hypergraph_deficit_h
  exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp0 j)) (pow_nonneg (by linarith) j))
    (pow_nonneg (add_nonneg (pow_nonneg hp0 j) (pow_nonneg (by linarith) j)) 2)

/-- Strict positivity of the hypergraph binomial deficit for n ≥ 3 and p in (0, 1/2). -/
theorem op_1668_hypergraph_binomial_deficit_pos (n : ℕ) (hn : 3 ≤ n) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1 / 2) : 0 < hypergraph_binomial_deficit n p := by
  have hpos : ∀ j, 0 < hypergraph_deficit_h p j := fun j => op_1668_hypergraph_binomial_deficit_pos_aux_pos p hp0 (by linarith) j
  have hnn : ∀ j, 0 ≤ hypergraph_deficit_h p j := fun j => op_1668_hypergraph_binomial_deficit_pos_aux_nonneg p (le_of_lt hp0) (by linarith) j
  have h1p : 0 < 1 - p := by linarith
  have hnpos : (0:ℝ) < ↑n := Nat.cast_pos.mpr (by omega)
  unfold hypergraph_binomial_deficit
  apply Finset.sum_pos'
  · intro w hw
    rw [Finset.mem_range] at hw
    have hwle : w ≤ n := by omega
    have hwleR : (↑w : ℝ) ≤ ↑n := Nat.cast_le.mpr hwle
    refine mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (le_of_lt hp0) w)) (pow_nonneg (le_of_lt h1p) (n - w))) ?_
    refine add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (hnn _)) ?_
    refine mul_nonneg (by norm_num) (add_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ (↑n : ℝ) - ↑w) (hnn _)) (mul_nonneg (Nat.cast_nonneg _) (hnn _)))
  · refine ⟨0, ?_, ?_⟩
    · rw [Finset.mem_range]; omega
    · have hA : 0 < (3 / 16 : ℝ) * ((↑n : ℝ) - 2 * (↑(0:ℕ) : ℝ)) ^ 2 * hypergraph_deficit_h p (Int.natAbs ((↑n : ℤ) - 2 * (↑(0:ℕ) : ℤ))) := by
        apply mul_pos
        · apply mul_pos (by norm_num)
          have hcast : ((↑n : ℝ) - 2 * (↑(0:ℕ) : ℝ)) = ↑n := by simp
          rw [hcast]; exact pow_pos hnpos 2
        · exact hpos _
      have hB : 0 ≤ (9 / 16 : ℝ) * (((↑n : ℝ) - (↑(0:ℕ) : ℝ)) * hypergraph_deficit_h p (Int.natAbs ((↑n : ℤ) - 2 * (↑(0:ℕ) : ℤ) - 1)) + (↑(0:ℕ) : ℝ) * hypergraph_deficit_h p (Int.natAbs ((↑n : ℤ) - 2 * (↑(0:ℕ) : ℤ) + 1))) := by
        refine mul_nonneg (by norm_num) (add_nonneg (mul_nonneg ?_ (hnn _)) (mul_nonneg (Nat.cast_nonneg _) (hnn _)))
        have hcast2 : ((↑n : ℝ) - (↑(0:ℕ) : ℝ)) = ↑n := by simp
        rw [hcast2]; exact le_of_lt hnpos
      refine mul_pos (mul_pos (mul_pos ?_ ?_) ?_) (add_pos_of_pos_of_nonneg hA hB)
      · rw [Nat.choose_zero_right]; norm_num
      · exact pow_pos hp0 0
      · exact pow_pos h1p (n - 0)
