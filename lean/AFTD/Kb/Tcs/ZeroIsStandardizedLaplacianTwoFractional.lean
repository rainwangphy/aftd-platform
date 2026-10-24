import AFTD.Prelude
import AFTD.Kb.Tcs.IsStandardizedLaplacianTwoFractional
import AFTD.Kb.Tcs.ZeroIsStandardizedLaplacian
import AFTD.Kb.Tcs.IsStandardizedLaplacian

/-!
# zero_is_standardized_laplacian_two_fractional

Topic: graphs   Node: 1ab98ffcb69b

Provenance: helper lemma. arXiv:2610.14100 Proposition 17

For any natural number n, the n by n zero matrix is a standardized Laplacian with at most two fractional entries per row.
-/

/-- The zero matrix is a standardized Laplacian with at most two fractional entries per row. -/
theorem zero_is_standardized_laplacian_two_fractional (n : ℕ) :
    is_standardized_laplacian_two_fractional n (0 : Matrix (Fin n) (Fin n) ℝ) := by
  refine ⟨zero_is_standardized_laplacian n, ?_⟩
  intro i
  simp
