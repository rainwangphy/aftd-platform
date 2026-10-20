import AFTD.Prelude

/-!
# poset_downset

Topic: combinatorics   Node: bf432432d76a

Provenance: formalization of a published result. Source: arXiv:2610.24774 Section 1

For a poset P and an element v in P, the strict downset D_P(v) is the set of all elements x in P strictly smaller than v.
-/

/-- The strict downset D_P(v) of an element v in a poset P. -/
def poset_downset {P : Type*} [PartialOrder P] (v : P) : Set P := {x | x < v}
