import AFTD.Prelude
import AFTD.Kb.Tcs.Bit
import AFTD.Kb.Tcs.DegreeSpace

/-!
# HasRealApproximation

Topic: circuits   Node: 38d4f5b0688c

Provenance: formalization of a published result. Source: arXiv:2610.19174 Listing A.1

For a Boolean function f : (Fin n → Bool) → Bool, natural number d, and real error ε, HasRealApproximation f d ε asserts the existence of a multilinear polynomial P : (Fin n → Bool) → ℝ in degreeSpace (K := ℝ) (Fin n) d such that |P x - bit (f x)| ≤ ε for all x : Fin n → Bool.
-/

/-- Existence of a degree-d real polynomial approximating a Boolean function f within error ε. -/
def HasRealApproximation {n : ℕ} (f : (Fin n → Bool) → Bool) (d : ℕ) (ε : ℝ) : Prop := ∃ P : (Fin n → Bool) → ℝ,
    P ∈ degreeSpace (K := ℝ) (Fin n) d ∧
    ∀ x, |P x - bit (f x)| ≤ ε
