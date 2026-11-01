import AFTD.Prelude

/-!
# arrangement3_u2

Topic: combinatorics   Node: 21eab443d305

Provenance: formalization of a published result. Source: arXiv:2610.38386, Section 5.1

The first row moment $U_2(S) = \sum_{i=0}^2 \sum_{j=0}^2 i \cdot ((S(i, j) : \mathbb{Z}) + 1)$ of an arrangement $S : \mathrm{Fin}\,3 \times \mathrm{Fin}\,3 \simeq \mathrm{Fin}\,9$.
-/

/-- The first row moment U2 of an order-3 arrangement. -/
def arrangement3_u2 (S : Fin 3 × Fin 3 ≃ Fin 9) : ℤ := ∑ i : Fin 3, ∑ j : Fin 3, (i : ℤ) * ((S (i, j)).val + 1 : ℤ)
