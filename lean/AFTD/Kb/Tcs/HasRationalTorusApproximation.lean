import AFTD.Prelude
import AFTD.Kb.Tcs.DegreeSpace
import AFTD.Kb.Tcs.Bit

/-!
# HasRationalTorusApproximation

Topic: circuits   Node: 7fbbe123dcb6

Provenance: original. Related work: arXiv:2610.19174, Majority and Torus Polynomials: Bounded-Lift Lower Bounds and Explicit Constructions

For a Boolean function f : (Fin n → Bool) → Bool on n variables, natural degree d, and error ε : ℝ, HasRationalTorusApproximation f d ε asserts the existence of a multilinear polynomial P : (Fin n → Bool) → ℚ in degreeSpace (K := ℚ) (Fin n) d and an integer lift Z : (Fin n → Bool) → ℤ such that |(P x : ℝ) - (Z x : ℝ) - bit (f x) / 2| ≤ ε for all x : Fin n → Bool.
-/

/-- Torus approximation by a multilinear polynomial with rational coefficients. -/
def HasRationalTorusApproximation {n : ℕ} (f : (Fin n → Bool) → Bool) (d : ℕ) (ε : ℝ) : Prop := ∃ P : (Fin n → Bool) → ℚ,
    P ∈ degreeSpace (K := ℚ) (Fin n) d ∧
    ∃ Z : (Fin n → Bool) → ℤ, ∀ x, |(P x : ℝ) - (Z x : ℝ) - bit (f x) / 2| ≤ ε
