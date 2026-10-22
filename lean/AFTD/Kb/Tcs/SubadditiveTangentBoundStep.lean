import AFTD.Prelude

/-!
# subadditive_tangent_bound_step

Topic: information   Node: 0c60a4871d57

Provenance: helper lemma. arXiv:2610.21231, Appendix C

If K_1 ≤ η_g, ℓ_g = η_g + K'_1, and K_x ≤ K_1 + K'_1 (x - 1), then η_g x + K_x ≤ 2 η_g + (x - 1) ℓ_g.
-/

/-- Tangent bound bounding η_g x + K_s(x) by 2 η_g + (x - 1) ℓ_g. -/
theorem subadditive_tangent_bound_step (η_g ℓ_g K1 K'1 x Kx : ℝ)
    (hℓ : ℓ_g = η_g + K'1)
    (hK1 : K1 ≤ η_g)
    (htan : Kx ≤ K1 + K'1 * (x - 1)) :
    η_g * x + Kx ≤ 2 * η_g + (x - 1) * ℓ_g := by
  calc
    η_g * x + Kx ≤ η_g * x + (K1 + K'1 * (x - 1)) := by linarith
    _ = K1 + η_g + (x - 1) * (η_g + K'1) := by ring
    _ = K1 + η_g + (x - 1) * ℓ_g := by rw [← hℓ]
    _ ≤ 2 * η_g + (x - 1) * ℓ_g := by linarith
