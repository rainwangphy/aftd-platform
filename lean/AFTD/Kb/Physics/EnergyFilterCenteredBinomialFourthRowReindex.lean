import AFTD.Prelude
import AFTD.Kb.Physics.EnergyFilterCenteredBinomialWeight
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# energy_filter_centered_binomial_fourth_row_reindex

Topic: statistical_mechanics   Node: 499804c30a5a

Provenance: helper lemma. OP-892: centered binomial fourth-mass asymptotic via rescaled step functions and dominated convergence.

For any natural k, the finite sum of the fourth powers of centered binomial weights equals the sum of the fourth powers of row 2k divided by the fourth power of its central coefficient.
-/

theorem energy_filter_centered_binomial_fourth_row_reindex (k : ℕ) :
    (∑ i ∈ Finset.Icc (-(k:ℤ)) (k:ℤ), energy_filter_centered_binomial_weight k i ^ 4) =
      (∑ j ∈ Finset.range (2*k+1), (Nat.choose (2*k) j : ℝ)^4) /
        (Nat.choose (2*k) k : ℝ)^4 := by
  rw [Finset.sum_div]
  apply Finset.sum_bij (fun i _ => ((k:ℤ)+i).toNat)
  · intro i hi
    rw [Finset.mem_Icc] at hi
    rw [Finset.mem_range]
    omega
  · intro a ha b hb hab
    rw [Finset.mem_Icc] at ha hb
    omega
  · intro j hj
    rw [Finset.mem_range] at hj
    refine ⟨(j:ℤ)-(k:ℤ), ?_, ?_⟩
    · rw [Finset.mem_Icc]
      omega
    · omega
  · intro i hi
    rw [Finset.mem_Icc] at hi
    simp [energy_filter_centered_binomial_weight, hi, div_pow]
