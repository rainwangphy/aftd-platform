import AFTD.Prelude

/-!
# is_affine_minimizer

Topic: submodular   Node: cd48e3059ee3

Provenance: formalization of a published result. Source: arXiv:2611.12680 Sec. 2.2

For a finite set T of vectors in ℝ^n, a vector w : Fin n → ℝ, and ambient weights μ : (Fin n → ℝ) → ℝ, is_affine_minimizer T w μ asserts that the sum of μ over T equals 1, μ vanishes outside T (μ p = 0 for all p ∉ T), w equals the linear combination ∑ p ∈ T, μ p • p, and the Euclidean inner product ∑ i : Fin n, w i * (p i - w i) equals 0 for every p ∈ T.
-/

/-- The affine minimizer of a finite set of points in ℝ^n, certified by affine weights vanishing outside T and orthogonality. -/
def is_affine_minimizer {n : ℕ} (T : Finset (Fin n → ℝ)) (w : Fin n → ℝ) (μ : (Fin n → ℝ) → ℝ) : Prop :=
  (∑ p ∈ T, μ p = 1) ∧
  (∀ p ∉ T, μ p = 0) ∧
  (w = ∑ p ∈ T, μ p • p) ∧
  (∀ p ∈ T, ∑ i : Fin n, w i * (p i - w i) = 0)
