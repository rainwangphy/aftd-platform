import AFTD.Prelude

/-!
# boolAnfCoefficient

Topic: circuits   Node: d1348b667ce4

Provenance: original. Related work: arXiv:2610.19174, Majority and Torus Polynomials: Bounded-Lift Lower Bounds and Explicit Constructions

For a Boolean function f : (Fin n → Bool) → Bool on n variables and a subset S : Finset (Fin n), the algebraic normal form coefficient boolAnfCoefficient f S is the Bool value indicating whether the number of inputs x : Fin n → Bool satisfying f x = true and x j = false for all j ∉ S is odd.
-/

/-- The algebraic normal form coefficient of a Bool-valued Boolean function at subset S. -/
def boolAnfCoefficient {n : ℕ} (f : (Fin n → Bool) → Bool) (S : Finset (Fin n)) : Bool := decide (Odd (Fintype.card { x : Fin n → Bool // f x = true ∧ ∀ j, j ∉ S → x j = false }))
