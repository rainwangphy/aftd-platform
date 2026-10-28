import AFTD.Prelude
import AFTD.Kb.Tcs.KstCodeMaxDensity
import AFTD.Kb.Tcs.K22CodeCardLe
import AFTD.Kb.Tcs.IsKstCode

/-!
# k22_code_max_density_le

Topic: combinatorics   Node: d45a9b2b789c

Provenance: formalization of a published result. Source: arXiv:2301.13305, Proposition 1.5; arXiv:2610.35136, Proposition 3.1

For every natural number n with 4 ≤ n, the maximum density of a K_{2,2}-code on Fin n, kst_code_max_density 2 2 n, is at most 1 / ((n : ℝ) - 2).
-/

/-- The maximum density of a K_{2,2}-code on Fin n for n ≥ 4 is at most 1 / (n - 2). -/
theorem k22_code_max_density_le (n : ℕ) (hn : 4 ≤ n) :
    kst_code_max_density 2 2 n ≤ 1 / ((n : ℝ) - 2) := by
  classical
  dsimp [kst_code_max_density]
  have hpos_n : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have h_le : ∀ C : Set (SimpleGraph (Fin n)),
      (⨆ (_hC : is_kst_code 2 2 n C), (Set.ncard C : ℝ) / (2 ^ (n.choose 2) : ℝ)) ≤ 1 / ((n : ℝ) - 2) := by
    intro C
    by_cases h : is_kst_code 2 2 n C
    · rw [ciSup_pos h]
      have hcard := k22_code_card_le n hn C h
      have hpos_pow : (0 : ℝ) < 2 ^ n.choose 2 := by positivity
      have hcast : ((n - 2 : ℕ) : ℝ) * (Set.ncard C : ℝ) ≤ (2 ^ n.choose 2 : ℝ) := by
        exact_mod_cast hcard
      have h_sub : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
        push_cast [show 2 ≤ n by omega]
        rfl
      rw [h_sub] at hcast
      rw [div_le_iff₀ hpos_pow]
      rw [div_mul_eq_mul_div, one_mul]
      rw [le_div_iff₀ hpos_n]
      linarith
    · rw [ciSup_neg h, Real.sSup_empty]
      positivity
  have : Nonempty (Set (SimpleGraph (Fin n))) := ⟨∅⟩
  exact ciSup_le h_le
