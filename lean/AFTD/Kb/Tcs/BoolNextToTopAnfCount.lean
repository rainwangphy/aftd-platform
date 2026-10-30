import AFTD.Prelude
import AFTD.Kb.Tcs.BoolAnfCoefficient

/-!
# boolNextToTopAnfCount

Topic: circuits   Node: 183fc81b7ccc

Provenance: original. Related work: arXiv:2610.19174, Majority and Torus Polynomials: Bounded-Lift Lower Bounds and Explicit Constructions

For a Boolean function f : (Fin n → Bool) → Bool on n variables, boolNextToTopAnfCount f is the number of indices i : Fin n such that the algebraic normal form coefficient boolAnfCoefficient f (Finset.univ \ {i}) is true.
-/

/-- The number of nonzero next-to-top ANF coefficients of a Boolean function. -/
def boolNextToTopAnfCount {n : ℕ} (f : (Fin n → Bool) → Bool) : ℕ := (Finset.univ.filter (fun i : Fin n => boolAnfCoefficient f (Finset.univ \ {i}))).card
