import AFTD.Prelude

/-!
# l2_norm_sq_c

Topic: circuits   Node: d457cea5d8db

Provenance: formalization of a published result. Source: scout/2611-06451-fourier-entropy-bounds-via-approximations.md:487

The squared L2 norm ||f||_2^2 of a function f : (Fin n -> Bool) -> ℂ with respect to the uniform distribution on the Boolean hypercube is defined by 2^(-n) * ∑_x |f(x)|^2.
-/

/-- Squared L2 norm of a complex function on the Boolean hypercube under the uniform distribution. -/
noncomputable def l2_norm_sq_c {n : ℕ} (f : (Fin n → Bool) → ℂ) : ℝ := (1 / (2 : ℝ) ^ n) * ∑ x : Fin n → Bool, ‖f x‖ ^ 2
