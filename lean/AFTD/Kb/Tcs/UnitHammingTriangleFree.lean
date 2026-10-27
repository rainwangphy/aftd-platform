import AFTD.Prelude

/-!
# unit_hamming_triangle_free

Topic: combinatorics   Node: fbf00aecb07e

Provenance: formalization of a published result. Source: arXiv:2610.32789 Definition 1.1

A finite set A : Finset (Fin n → Fin q) is unit_hamming_triangle_free if for all x, y, z : Fin n → Fin q, if x ∈ A, y ∈ A, z ∈ A, and x ≠ y, y ≠ z, and x ≠ z, then it is not the case that hammingDist x y = 1, hammingDist y z = 1, and hammingDist x z = 1.
-/

/-- Predicate that a finite set of words in [q]^n induces a triangle-free subgraph in the unit-distance Hamming graph. -/
def unit_hamming_triangle_free {n q : ℕ} (A : Finset (Fin n → Fin q)) : Prop := ∀ ⦃x y z : Fin n → Fin q⦄, x ∈ A → y ∈ A → z ∈ A →
    x ≠ y → y ≠ z → x ≠ z →
    ¬(hammingDist x y = 1 ∧ hammingDist y z = 1 ∧ hammingDist x z = 1)
