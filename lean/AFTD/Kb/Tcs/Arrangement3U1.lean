import AFTD.Prelude

/-!
# arrangement3_u1

Topic: combinatorics   Node: a47246300fe3

Provenance: formalization of a published result. Source: arXiv:2610.38386, Section 5.1

The first column moment $U_1(S) = \sum_{i=0}^2 \sum_{j=0}^2 j \cdot ((S(i, j) : \mathbb{Z}) + 1)$ of an arrangement $S : \mathrm{Fin}\,3 \times \mathrm{Fin}\,3 \simeq \mathrm{Fin}\,9$.
-/

/-- The first column moment U1 of an order-3 arrangement. -/
def arrangement3_u1 (S : Fin 3 × Fin 3 ≃ Fin 9) : ℤ := ∑ i : Fin 3, ∑ j : Fin 3, (j : ℤ) * ((S (i, j)).val + 1 : ℤ)
