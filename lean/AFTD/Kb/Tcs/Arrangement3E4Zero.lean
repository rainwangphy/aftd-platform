import AFTD.Prelude

/-!
# arrangement3_e4_zero

Topic: combinatorics   Node: c38885674478

Provenance: formalization of a published result. Source: arXiv:2610.38386, Definition 2.4 and Section 5.1

The four-term line-sum energy zero condition $E_4(S) = 0$ for an arrangement $S : \mathrm{Fin}\,3 \times \mathrm{Fin}\,3 \simeq \mathrm{Fin}\,9$, asserting that the column moment $\sum_{i=0}^2 \sum_{j=0}^2 j(S(i,j)+1) = 45$, the row moment $\sum_{i=0}^2 \sum_{j=0}^2 i(S(i,j)+1) = 45$, the main diagonal sum $\sum_{i=0}^2 (S(i,i)+1) = 15$, and the anti-diagonal sum $\sum_{i=0}^2 (S(i, 2-i)+1) = 15$.
-/

/-- The four-term line-sum energy zero condition E4(S) = 0 for an order-3 arrangement. -/
def arrangement3_e4_zero (S : Fin 3 × Fin 3 ≃ Fin 9) : Prop :=
  (∑ i : Fin 3, ∑ j : Fin 3, (j : ℤ) * ((S (i, j)).val + 1 : ℤ) = 45) ∧
  (∑ i : Fin 3, ∑ j : Fin 3, (i : ℤ) * ((S (i, j)).val + 1 : ℤ) = 45) ∧
  (∑ i : Fin 3, ((S (i, i)).val + 1 : ℤ) = 15) ∧
  (∑ i : Fin 3, ((S (i, Fin.rev i)).val + 1 : ℤ) = 15)
