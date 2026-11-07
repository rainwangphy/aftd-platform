import AFTD.Prelude

/-!
# carpool_threshold_A

Topic: online_algorithms   Node: bcf8e09d0094

Provenance: formalization of a published result. Source: arXiv:2611.00388 Eq. (4.2)

The quadratic threshold function carpool_threshold_A taking an integer parameter D : ℤ and a natural number k : ℕ, defined as the integer (k : ℤ) * D - 15 * (k : ℤ) * ((k : ℤ) - 1).
-/

/-- Quadratic threshold A(k) = k * D - 15 * k * (k - 1) for carpooling backward step analysis. -/
def carpool_threshold_A (D : ℤ) (k : ℕ) : ℤ := (k : ℤ) * D - 15 * (k : ℤ) * ((k : ℤ) - 1)
