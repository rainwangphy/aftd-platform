import AFTD.Prelude

/-!
# incidence_vector

Topic: combinatorics   Node: 111e66163ed7

Provenance: formalization of a published result. Source: arXiv:2611.20197

Given a type R equipped with 0 and 1, a natural number N, and a subset E : Finset (Fin N), incidence_vector E is the function Fin N → R mapping each index j to 1 if j ∈ E, and 0 otherwise.
-/

/-- The incidence vector 1_E in Fin N → R of a subset E of Fin N. -/
def incidence_vector {N : ℕ} {R : Type*} [Zero R] [One R] (E : Finset (Fin N)) : Fin N → R :=
  fun j => if j ∈ E then 1 else 0
