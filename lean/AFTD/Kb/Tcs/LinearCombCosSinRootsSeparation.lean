import AFTD.Prelude

/-!
# linear_comb_cos_sin_roots_separation

Topic: combinatorics   Node: a7370b594cee

Provenance: helper lemma. arXiv:2610.38368 Lemma 2.1

Let c, d be real numbers not both zero. If t₁ < t₂ and t₂ - t₁ < π, then c * cos t + d * sin t cannot vanish at both t₁ and t₂.
-/

/-- A nonzero linear combination of cosine and sine cannot have two roots whose distance is less than π. -/
theorem linear_comb_cos_sin_roots_separation (c d t₁ t₂ : ℝ)
    (hcd : c ≠ 0 ∨ d ≠ 0) (hlt : t₁ < t₂) (hdist : t₂ - t₁ < Real.pi)
    (hzero₁ : c * Real.cos t₁ + d * Real.sin t₁ = 0)
    (hzero₂ : c * Real.cos t₂ + d * Real.sin t₂ = 0) : False := by
  have hpos : 0 < t₂ - t₁ := sub_pos.mpr hlt
  have hsin_pos : 0 < Real.sin (t₂ - t₁) :=
    Real.sin_pos_of_mem_Ioo ⟨hpos, hdist⟩
  have h1 : c * Real.sin (t₂ - t₁) = 0 := by
    calc c * Real.sin (t₂ - t₁)
      _ = (c * Real.cos t₁ + d * Real.sin t₁) * Real.sin t₂ -
          (c * Real.cos t₂ + d * Real.sin t₂) * Real.sin t₁ := by
        rw [Real.sin_sub]; ring
      _ = 0 := by rw [hzero₁, hzero₂]; ring
  have h2 : d * Real.sin (t₂ - t₁) = 0 := by
    calc d * Real.sin (t₂ - t₁)
      _ = (c * Real.cos t₂ + d * Real.sin t₂) * Real.cos t₁ -
          (c * Real.cos t₁ + d * Real.sin t₁) * Real.cos t₂ := by
        rw [Real.sin_sub]; ring
      _ = 0 := by rw [hzero₁, hzero₂]; ring
  have hsin_zero : Real.sin (t₂ - t₁) = 0 := by
    rcases hcd with hc | hd
    · exact (mul_eq_zero.mp h1).resolve_left hc
    · exact (mul_eq_zero.mp h2).resolve_left hd
  linarith
