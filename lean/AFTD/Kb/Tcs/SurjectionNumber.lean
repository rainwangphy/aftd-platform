import AFTD.Prelude

/-!
# surjection_number

Topic: combinatorics   Node: 9f8d17ca7e32

Provenance: formalization of a published result. Source: arXiv:2611.11056, Section 4

The surjection number U_l(t) is defined as l! S(t, l), representing the number of surjections from a t-element set to an l-element set, where S(t, l) is the Stirling number of the second kind.
-/

/-- The number of surjections from a t-element set to an l-element set, defined as l! * S(t, l). -/
def surjection_number (l t : ℕ) : ℕ := l.factorial * Nat.stirlingSecond t l
