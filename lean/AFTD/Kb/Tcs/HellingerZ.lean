import AFTD.Prelude
import AFTD.Kb.Tcs.NoiseOperator

/-!
# hellinger_Z

Topic: information   Node: 0ec38a152485

Provenance: formalization of a published result. Source: scout/2610-10618-the-hellinger-conjecture-for-antipodal-boolean-functions.md:164

The Hellinger affinity Z_rho(f) of a Boolean function f is the expected value over uniform Y of sqrt(1 - (T_rho f(Y))^2).
-/

open scoped BigOperators in
/-- The Hellinger affinity quantity Z_rho(f) = E_Y sqrt(1 - (T_rho f(Y))^2). -/
noncomputable def hellinger_Z (n : ℕ) (ρ : ℝ) (f : (Fin n → Bool) → ℝ) : ℝ := (1 / (2 : ℝ) ^ n) * ∑ y : Fin n → Bool, Real.sqrt (1 - (noise_operator n ρ f y) ^ 2)
