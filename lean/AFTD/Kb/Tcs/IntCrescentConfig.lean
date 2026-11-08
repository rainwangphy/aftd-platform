import AFTD.Prelude
import AFTD.Kb.Tcs.IntCrescentPoint

/-!
# int_crescent_config

Topic: combinatorics   Node: 3295bce418c7

Provenance: formalization of a published result. Source: arXiv:2610.38368 Section 3

For a natural number n, int_crescent_config n is the finite set in Finset (Fin 3 → ℤ) given by the image of Finset.univ under int_crescent_point n.
-/

/-- The n-point integer configuration in ℤ^3 formed by the points int_crescent_point n j for j in Fin n. -/
def int_crescent_config (n : ℕ) : Finset (Fin 3 → ℤ) := Finset.univ.image (int_crescent_point n)
