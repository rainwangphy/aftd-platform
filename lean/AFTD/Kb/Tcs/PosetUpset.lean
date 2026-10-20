import AFTD.Prelude

/-!
# poset_upset

Topic: combinatorics   Node: 858f4460b423

Provenance: formalization of a published result. Source: arXiv:2610.24774 Section 1

For a poset P and an element u in P, the strict upset U_P(u) is the set of all elements y in P strictly greater than u.
-/

/-- The strict upset U_P(u) of an element u in a poset P. -/
def poset_upset {P : Type*} [PartialOrder P] (u : P) : Set P := {y | u < y}
