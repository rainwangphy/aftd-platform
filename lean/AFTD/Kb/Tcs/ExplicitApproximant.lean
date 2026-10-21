import AFTD.Prelude
import AFTD.Kb.Tcs.TopCoefficient
import AFTD.Kb.Tcs.FullMonomial
import AFTD.Kb.Tcs.ParityCharacter

/-!
# explicitApproximant

Topic: circuits   Node: a41b9b64b1cc

Provenance: formalization of a published result. Source: arXiv:2610.19174, Theorem 4.1.1 eq (6) and Listing A.13

For a Boolean function f : (Fin n → Bool) → Bool and input x : Fin n → Bool, explicitApproximant f x is (if f x then 1 else 0)/2 - (topCoefficient f / 2 : ℤ) * fullMonomial x - (topCoefficient f % 2 : ℤ) * parityCharacter x / 2^(n + 1).
-/

/-- The explicit approximating polynomial of degree at most n - 1 evaluated at x. -/
noncomputable def explicitApproximant {n : ℕ} (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) : ℝ := (if f x then (1 : ℝ) else 0) / 2 -
  ((topCoefficient f / 2 : ℤ) : ℝ) * fullMonomial x -
  ((topCoefficient f % 2 : ℤ) : ℝ) * parityCharacter x / (2 : ℝ) ^ (n + 1)
