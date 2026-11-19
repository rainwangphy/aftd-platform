import AFTD.Prelude

/-!
# explicit_witness_vector_32

Topic: combinatorics   Node: d968888e4aa8

Provenance: formalization of a published result. Source: arXiv:2611.23269, Eq. (4)

The integer vector x of type Fin 32 → ℤ with entries -10, 24, -18, 0, -23, 1, -2, -6, -3, 10, -15, -35, -14, -34, 10, 17, 6, -4, 38, 31, -3, 22, -31, -10, -1, 31, -1, -1, 8, 7, 9, -2.
-/

/-- The integer witness vector of length 32 whose Rayleigh quotient exceeds the permanent. -/
def explicit_witness_vector_32 : Fin 32 → ℤ :=
  ![-10, 24, -18, 0, -23, 1, -2, -6, -3, 10, -15, -35, -14, -34, 10, 17,
    6, -4, 38, 31, -3, 22, -31, -10, -1, 31, -1, -1, 8, 7, 9, -2]
