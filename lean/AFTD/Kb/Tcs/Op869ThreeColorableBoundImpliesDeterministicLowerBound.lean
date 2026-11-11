import AFTD.Prelude
import AFTD.Kb.Tcs.IsOnlineColoringAlg
import AFTD.Kb.Tcs.ProperlyColorsKColorable
import AFTD.Kb.Tcs.ColorsUsed

/-!
# op869_three_colorable_bound_implies_deterministic_lower_bound

Topic: online_algorithms   Node: be80a2a0d96a

Provenance: helper lemma. Reduction for OP-869 using arXiv:2610.41516 Theorem 1.1; this conditional lemma does not assume that theorem is proved in Lean.

If the three-colorable deterministic online coloring lower bound of arXiv:2610.41516 Theorem 1.1 holds in the stated finite-graph model, then the requested deterministic lower bound for k-colorable graphs holds for every k at least four.
-/

private lemma op869_weighted_pow_mono (x y a b : ℝ) (hy : 0 < y) (hyx : y ≤ x) (hab : a ≤ b) :
    x ^ a * y ^ (1 - a) ≤ x ^ b * y ^ (1 - b) := by
  have hx : 0 < x := lt_of_lt_of_le hy hyx
  rw [Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hy,
      Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hy,
      ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hl : Real.log y ≤ Real.log x := Real.log_le_log hy hyx
  nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hl)]

private lemma op869_exponent_compare (k : ℕ) (hk : 4 ≤ k) :
    (1 : ℝ) / ((k : ℝ) - 1) ≤ (1 : ℝ) / 3 := by
  have hk' : (4 : ℝ) ≤ k := by exact_mod_cast hk
  apply (div_le_div_iff₀ (by linarith : 0 < (k : ℝ) - 1) (by norm_num : (0 : ℝ) < 3)).2
  linarith

private lemma op869_target_compare (k : ℕ) (hk : 4 ≤ k) (n : ℕ) (hn : Real.exp 1 < n) :
    Real.log (n : ℝ) ^ ((1 : ℝ) / ((k : ℝ) - 1)) *
      Real.log (Real.log (n : ℝ)) ^ (((k : ℝ) - 2) / ((k : ℝ) - 1)) ≤
    Real.log (n : ℝ) ^ ((1 : ℝ) / 3) * Real.log (Real.log (n : ℝ)) ^ ((2 : ℝ) / 3) := by
  have hnpos : (0 : ℝ) < n := lt_trans (Real.exp_pos 1) hn
  have hlog : 1 < Real.log (n : ℝ) := by
    have := Real.log_lt_log (Real.exp_pos 1) hn
    simpa using this
  have hy : 0 < Real.log (Real.log (n : ℝ)) := Real.log_pos hlog
  have hyx : Real.log (Real.log (n : ℝ)) ≤ Real.log (n : ℝ) := Real.log_le_self (by linarith)
  have hk' : (4 : ℝ) ≤ k := by exact_mod_cast hk
  have heq : ((k : ℝ) - 2) / ((k : ℝ) - 1) = 1 - 1 / ((k : ℝ) - 1) := by
    field_simp [ne_of_gt (show (0 : ℝ) < (k : ℝ) - 1 by linarith)]
    <;> ring
  rw [heq]
  convert op869_weighted_pow_mono (Real.log (n : ℝ)) (Real.log (Real.log (n : ℝ)))
    (1 / ((k : ℝ) - 1)) (1 / 3) hy hyx (op869_exponent_compare k hk) using 1 <;> norm_num

theorem op869_three_colorable_bound_implies_deterministic_lower_bound (hthree : ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ A : SimpleGraph (Fin n) → (Fin n → ℕ),
        IsOnlineColoringAlg A → ProperlyColorsKColorable 3 A →
          ∃ G : SimpleGraph (Fin n), G.Colorable 3 ∧
            Real.exp (c * (Real.log (n : ℝ) ^ ((1 : ℝ) / 3)) *
              (Real.log (Real.log (n : ℝ)) ^ ((2 : ℝ) / 3))) ≤ (colorsUsed (A G) : ℝ))
    (k : ℕ) (hk : 4 ≤ k) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ A : SimpleGraph (Fin n) → (Fin n → ℕ),
        IsOnlineColoringAlg A → ProperlyColorsKColorable k A →
          ∃ G : SimpleGraph (Fin n), G.Colorable k ∧
            Real.exp (c * (Real.log (n : ℝ) ^ ((1 : ℝ) / ((k : ℝ) - 1))) *
              (Real.log (Real.log (n : ℝ)) ^ (((k : ℝ) - 2) / ((k : ℝ) - 1)))) ≤ (colorsUsed (A G) : ℝ) := by
  obtain ⟨c, hc, n₀, hthree⟩ := hthree
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp 1)
  refine ⟨c, hc, max n₀ N, ?_⟩
  intro n hn A hA hproper
  have hn' : Real.exp 1 < (n : ℝ) := lt_of_lt_of_le hN (by exact_mod_cast (le_trans (le_max_right n₀ N) hn))
  have hproper3 : ProperlyColorsKColorable 3 A := by
    intro G hG u v huv
    exact hproper G (hG.mono (by omega)) u v huv
  obtain ⟨G, hG, hbound⟩ := hthree n (le_trans (le_max_left n₀ N) hn) A hA hproper3
  refine ⟨G, hG.mono (by omega), ?_⟩
  apply le_trans _ hbound
  apply Real.exp_le_exp.mpr
  have hcomp := op869_target_compare k hk n hn'
  nlinarith [mul_nonneg (le_of_lt hc) (sub_nonneg.mpr hcomp)]
