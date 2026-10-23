import AFTD.Prelude

/-!
# strictMajority

Topic: circuits   Node: 1565eb7dc3de

Provenance: formalization of a published result. Source: arXiv:2610.19174 Section 4.2

The strict Majority function on n Boolean inputs, returning true if strictly more than n/2 inputs are true, and false otherwise.
-/

/-- The strict Majority function on n Boolean inputs, outputting true iff strictly more than n/2 inputs are true. -/
def strictMajority (n : ℕ) (x : Fin n → Bool) : Bool := decide (n < 2 * (Finset.univ.filter (fun i => x i = true)).card)
