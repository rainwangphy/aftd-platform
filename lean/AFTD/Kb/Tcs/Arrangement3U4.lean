import AFTD.Prelude

/-!
# arrangement3_u4

Topic: combinatorics   Node: b9e7d6183d9a

Provenance: formalization of a published result. Source: arXiv:2610.38386, Section 5.1

The anti-diagonal sum $U_4(S) = \sum_{i=0}^2 ((S(i, \mathrm{rev}(i)) : \mathbb{Z}) + 1)$ of an arrangement $S : \mathrm{Fin}\,3 \times \mathrm{Fin}\,3 \simeq \mathrm{Fin}\,9$.
-/

/-- The anti-diagonal sum U4 of an order-3 arrangement. -/
def arrangement3_u4 (S : Fin 3 × Fin 3 ≃ Fin 9) : ℤ := ∑ i : Fin 3, ((S (i, Fin.rev i)).val + 1 : ℤ)
