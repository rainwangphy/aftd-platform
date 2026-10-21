import AFTD.Prelude
import AFTD.Kb.Tcs.Bit
import AFTD.Kb.Tcs.DegreeSpace

/-!
# HasTorusApproximation

Topic: circuits   Node: 7be3add07535

Provenance: formalization of a published result. Source: arXiv:2610.19174, Listing A.1

For a Boolean function f : (Fin n → Bool) → Bool, natural number d, and real error ε, HasTorusApproximation f d ε asserts the existence of a multilinear polynomial P : (Fin n → Bool) → ℝ in degreeSpace (K := ℝ) (Fin n) d and an integer lift Z : (Fin n → Bool) → ℤ such that |P x - Z x - bit (f x) / 2| ≤ ε for all x : Fin n → Bool.
-/

/-- Predicate asserting that f has a torus polynomial approximation of degree at most d with error at most ε. -/
def HasTorusApproximation {n : ℕ} (f : (Fin n → Bool) → Bool) (d : ℕ) (ε : ℝ) : Prop := ∃ P : (Fin n → Bool) → ℝ,
    P ∈ degreeSpace (K := ℝ) (Fin n) d ∧
    ∃ Z : (Fin n → Bool) → ℤ, ∀ x, |P x - (Z x : ℝ) - bit (f x) / 2| ≤ ε
