import AFTD.Prelude
import AFTD.Kb.Tcs.HasTorusApproximation

/-!
# optimalTorusError

Topic: circuits   Node: 318079ca5bb6

Provenance: formalization of a published result. Source: arXiv:2610.19174, Section 2.1 and Listing A.1

For a Boolean function f : (Fin n → Bool) → Bool and natural number d, optimalTorusError f d is the real infimum of all errors ε : ℝ such that HasTorusApproximation f d ε holds.
-/

/-- Optimal torus approximation error of degree at most d for a Boolean function f. -/
noncomputable def optimalTorusError {n : ℕ} (f : (Fin n → Bool) → Bool) (d : ℕ) : ℝ := sInf { ε : ℝ | HasTorusApproximation f d ε }
