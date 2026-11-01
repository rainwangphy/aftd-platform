import AFTD.Prelude

/-!
# noise_operator

Topic: information   Node: 286b95ed1b73

Provenance: formalization of a published result. Source: scout/2610-10618-the-hellinger-conjecture-for-antipodal-boolean-functions.md:162

The noise operator T_rho f on the Boolean cube is the conditional expectation E[f(X) | Y = y] where each bit of X is flipped independently with probability (1 - rho) / 2.
-/

open scoped BigOperators in
/-- The Bonami-Beckner noise operator T_rho f(y) = E[f(X) | Y = y] for the binary symmetric channel. -/
noncomputable def noise_operator (n : ℕ) (ρ : ℝ) (f : (Fin n → Bool) → ℝ) (y : Fin n → Bool) : ℝ := ∑ x : Fin n → Bool,
    (((1 + ρ) / 2) ^ (n - hammingDist x y) * ((1 - ρ) / 2) ^ (hammingDist x y)) * f x
