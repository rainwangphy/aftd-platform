import AFTD.Prelude

/-!
# zycle

Topic: combinatorics   Node: 3498a3629397

Provenance: formalization of a published result. Source: arXiv:2611.12582 Section 1

For any positive integer ℓ, the 3-uniform zycle Z_ℓ has vertex set ZMod ℓ × Fin 2 and edge set consisting of the triples {(i,0), (i,1), (i+1,0)} and {(i,0), (i,1), (i+1,1)} for all i in ZMod ℓ.
-/

/-- The 3-uniform zycle Z_ℓ with vertices x_i = (i,0) and y_i = (i,1) for i in ZMod ℓ and edges {x_i, y_i, x_{i+1}} and {x_i, y_i, y_{i+1}}. -/
def zycle (ℓ : ℕ) [NeZero ℓ] : Finset (Finset (ZMod ℓ × Fin 2)) := Finset.univ.biUnion fun (i : ZMod ℓ) =>
    { {(i, 0), (i, 1), (i + 1, 0)}, {(i, 0), (i, 1), (i + 1, 1)} }
