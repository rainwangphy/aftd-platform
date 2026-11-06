import AFTD.Prelude

/-!
# is_p_star_kappa

Topic: lp_duality   Node: 4b0202908eac

Provenance: formalization of a published result. Source: arXiv:2611.07815 Section 1 (equation 1)

A square real matrix M belongs to the class P*(κ) for a parameter κ ≥ 0 if for all x, the sum (1 + 4κ) ∑_{i: x_i (Mx)_i > 0} x_i (Mx)_i + ∑_{i: x_i (Mx)_i < 0} x_i (Mx)_i is nonnegative.
-/

/-- A square real matrix belongs to P*(κ) if (1 + 4κ) times its positive coordinate products plus its negative coordinate products is nonnegative for all vectors. -/
def is_p_star_kappa (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (κ : ℝ) : Prop := 0 ≤ κ ∧ ∀ x : Fin n → ℝ,
    0 ≤ (1 + 4 * κ) * (∑ i ∈ Finset.univ.filter (fun i => 0 < x i * (Matrix.mulVec M x) i), x i * (Matrix.mulVec M x) i) +
      (∑ i ∈ Finset.univ.filter (fun i => x i * (Matrix.mulVec M x) i < 0), x i * (Matrix.mulVec M x) i)
