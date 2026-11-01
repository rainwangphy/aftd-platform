import AFTD.Prelude

/-!
# arrangement3_u3

Topic: combinatorics   Node: b839e8af932c

Provenance: formalization of a published result. Source: arXiv:2610.38386, Section 5.1

The main diagonal sum $U_3(S) = \sum_{i=0}^2 ((S(i, i) : \mathbb{Z}) + 1)$ of an arrangement $S : \mathrm{Fin}\,3 \times \mathrm{Fin}\,3 \simeq \mathrm{Fin}\,9$.
-/

/-- The main diagonal sum U3 of an order-3 arrangement. -/
def arrangement3_u3 (S : Fin 3 × Fin 3 ≃ Fin 9) : ℤ := ∑ i : Fin 3, ((S (i, i)).val + 1 : ℤ)
