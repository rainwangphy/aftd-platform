import AFTD.Prelude

/-!
# nonzero_cubes

Topic: cryptography   Node: 3c6ae0a989b5

Provenance: formalization of a published result. Source: arXiv:2611.10269 Sec. 7

The set of nonzero cubes in a field E, consisting of all elements of the form x^3 for nonzero x in E.
-/

/-- The set of nonzero cubes in a field E. -/
def nonzero_cubes (E : Type*) [Field E] : Set E := {y : E | ∃ x : E, x ≠ 0 ∧ x ^ 3 = y}
