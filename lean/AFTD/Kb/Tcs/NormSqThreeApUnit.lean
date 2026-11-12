import AFTD.Prelude

/-!
# norm_sq_three_ap_unit

Topic: combinatorics   Node: 4e51d1ccda8a

Provenance: formalization of a published result. Source: arXiv:2611.12360, Lemma 2.1

For any 3-term arithmetic progression x₀, x₀ + v, x₀ + 2 • v in n-dimensional Euclidean space with unit spacing ||v|| = 1, the alternating sum ||x₀||^2 - 2 * ||x₀ + v||^2 + ||x₀ + 2 • v||^2 equals 2.
-/

/-- Second difference identity of squared norms for a 3-term arithmetic progression with unit spacing. -/
theorem norm_sq_three_ap_unit {n : ℕ} (x₀ v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ = 1) :
    ‖x₀‖ ^ 2 - 2 * ‖x₀ + v‖ ^ 2 + ‖x₀ + (2 : ℝ) • v‖ ^ 2 = 2 := by
  rw [norm_add_sq_real x₀ v]
  rw [norm_add_sq_real x₀ ((2 : ℝ) • v)]
  rw [inner_smul_right]
  rw [norm_smul]
  rw [hv]
  norm_num
  ring
