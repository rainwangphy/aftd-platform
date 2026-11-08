import AFTD.Prelude

/-!
# cos_sin_comb_at_most_one_root

Topic: combinatorics   Node: 16245552f154

Provenance: helper lemma. arXiv:2610.38368, Lemma 2.1

If a linear combination c * cos t + d * sin t has two distinct roots in an open interval (a, b) of length less than π, then both coefficients c and d must be zero.
-/

/-- A nonzero linear combination of cosine and sine has at most one zero in any interval of length less than π. -/
theorem cos_sin_comb_at_most_one_root (c d a b : ℝ) (hab : b - a < Real.pi)
    (t₁ t₂ : ℝ) (h₁ : t₁ ∈ Set.Ioo a b) (h₂ : t₂ ∈ Set.Ioo a b)
    (heq₁ : c * Real.cos t₁ + d * Real.sin t₁ = 0)
    (heq₂ : c * Real.cos t₂ + d * Real.sin t₂ = 0)
    (hlt : t₁ < t₂) : c = 0 ∧ d = 0 := by
  have h_mem : t₂ - t₁ ∈ Set.Ioo 0 Real.pi := by
    rw [Set.mem_Ioo] at h₁ h₂ ⊢
    exact ⟨by linarith, by linarith⟩
  have h_sin_pos : 0 < Real.sin (t₂ - t₁) := Real.sin_pos_of_mem_Ioo h_mem
  have h_sin_ne : Real.sin (t₂ - t₁) ≠ 0 := ne_of_gt h_sin_pos
  have hc : c * Real.sin (t₂ - t₁) = 0 := by
    calc
      c * Real.sin (t₂ - t₁) = Real.sin t₂ * (c * Real.cos t₁ + d * Real.sin t₁) - Real.sin t₁ * (c * Real.cos t₂ + d * Real.sin t₂) := by
        rw [Real.sin_sub]; ring
      _ = Real.sin t₂ * 0 - Real.sin t₁ * 0 := by rw [heq₁, heq₂]
      _ = 0 := by ring
  have hd : d * Real.sin (t₂ - t₁) = 0 := by
    calc
      d * Real.sin (t₂ - t₁) = Real.cos t₁ * (c * Real.cos t₂ + d * Real.sin t₂) - Real.cos t₂ * (c * Real.cos t₁ + d * Real.sin t₁) := by
        rw [Real.sin_sub]; ring
      _ = Real.cos t₁ * 0 - Real.cos t₂ * 0 := by rw [heq₁, heq₂]
      _ = 0 := by ring
  exact ⟨(mul_eq_zero.mp hc).resolve_right h_sin_ne,
         (mul_eq_zero.mp hd).resolve_right h_sin_ne⟩
