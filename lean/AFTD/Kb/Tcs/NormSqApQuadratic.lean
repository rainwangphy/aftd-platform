import AFTD.Prelude

/-!
# norm_sq_ap_quadratic

Topic: combinatorics   Node: ec600ee96b52

Provenance: formalization of a published result. Source: arXiv:2611.12360, Lemma 2.1

For any initial point x₀ and difference vector v in n-dimensional Euclidean space, and any real coefficient k, the squared norm of x₀ + k • v is given by ||v||^2 * k^2 + 2 * ⟪x₀, v⟫ * k + ||x₀||^2.
-/

/-- Quadratic identity for the squared Euclidean norm of points along an arithmetic progression. -/
theorem norm_sq_ap_quadratic {n : ℕ} (x₀ v : EuclideanSpace ℝ (Fin n)) (k : ℝ) :
    ‖x₀ + k • v‖ ^ 2 = ‖v‖ ^ 2 * k ^ 2 + 2 * @inner ℝ _ _ x₀ v * k + ‖x₀‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_comm x₀ v]
  ring
