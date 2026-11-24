import AFTD.Prelude

/-!
# is_ternary_matrix

Topic: combinatorics   Node: e887e94239de

Provenance: formalization of a published result. Source: arXiv:2611.27591 Sec. 1

A complex matrix is ternary if each of its entries is a complex third root of unity.
-/

/-- A complex matrix whose entries lie in the group of complex third roots of unity. -/
def is_ternary_matrix {m n : Type*} (M : Matrix m n ℂ) : Prop := ∀ i j, ∃ u : rootsOfUnity 3 ℂ, ((u : ℂˣ) : ℂ) = M i j
