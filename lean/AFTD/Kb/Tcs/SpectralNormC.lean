import AFTD.Prelude

/-!
# spectral_norm_c

Topic: circuits   Node: 619242de88ed

Provenance: formalization of a published result. Source: scout/2611-06451-fourier-entropy-bounds-via-approximations.md:502

The spectral norm ||f_hat||_1 of a function f : (Fin n -> Bool) -> ℂ is defined as the sum over all subsets S of Fin n of the absolute value of the Fourier coefficient f_hat(S) = 2^(-n) * ∑_x f(x) ∏_{i ∈ S} (if x(i) then -1 else 1).
-/

/-- Spectral norm (L1 norm of Fourier coefficients) of a complex function on the Boolean hypercube. -/
noncomputable def spectral_norm_c {n : ℕ} (f : (Fin n → Bool) → ℂ) : ℝ := ∑ S : Finset (Fin n), ‖(1 / (2 : ℂ) ^ n) * ∑ x : Fin n → Bool, f x * (∏ i ∈ S, if x i then (-1 : ℂ) else 1)‖
