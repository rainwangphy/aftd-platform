import AFTD.Prelude

/-!
# frobenius_extremal_family

Topic: elementary_number_theory   Node: 711c143d6d5a

Provenance: formalization of a published result. Source: scout/2610-32219-a-sharp-upper-bound-for-the-frobenius-number.md:454

For natural numbers n and q, `frobenius_extremal_family n q` is the set of natural numbers consisting of all multiples i * q for 1 ≤ i ≤ n - 1, together with (n - 2) * q + 1.
-/

/-- The extremal family S_{n,q} = {i * q | 1 ≤ i ≤ n - 1} ∪ {(n - 2) * q + 1} for the Frobenius number bound. -/
def frobenius_extremal_family (n q : ℕ) : Set ℕ := {x | ∃ i, 1 ≤ i ∧ i ≤ n - 1 ∧ x = i * q} ∪ {(n - 2) * q + 1}
