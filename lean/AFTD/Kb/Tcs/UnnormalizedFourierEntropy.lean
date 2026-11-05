import AFTD.Prelude

/-!
# unnormalized_fourier_entropy

Topic: circuits   Node: 72066080cafb

Provenance: formalization of a published result. Source: scout/2611-06451-fourier-entropy-bounds-via-approximations.md:559

The unnormalized Fourier entropy functional ℍ(f_hat^2) of a function f : (Fin n -> Bool) -> ℂ is defined as the sum over all subsets S of Fin n of 0 if |f_hat(S)| = 0, and |f_hat(S)|^2 * log_2(1 / |f_hat(S)|^2) otherwise, where f_hat(S) = 2^(-n) * ∑_x f(x) ∏_{i ∈ S} (if x(i) then -1 else 1).
-/

/-- Unnormalized Fourier entropy functional of a complex function on the Boolean hypercube. -/
noncomputable def unnormalized_fourier_entropy {n : ℕ} (f : (Fin n → Bool) → ℂ) : ℝ := open Classical in
  ∑ S : Finset (Fin n),
    let c := (1 / (2 : ℂ) ^ n) * ∑ x : Fin n → Bool, f x * (∏ i ∈ S, if x i then (-1 : ℂ) else 1)
    if ‖c‖ = 0 then 0
    else ‖c‖ ^ 2 * Real.logb 2 (1 / ‖c‖ ^ 2)
