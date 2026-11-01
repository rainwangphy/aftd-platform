import AFTD.Prelude

/-!
# is_magic_arrangement3

Topic: combinatorics   Node: 31acb39296a0

Provenance: formalization of a published result. Source: arXiv:2610.38386, Proposition 5.1

An arrangement $S : \mathrm{Fin}\,3 \times \mathrm{Fin}\,3 \simeq \mathrm{Fin}\,9$ is a magic square if every row sum $\sum_{j=0}^2 (S(i,j)+1) = 15$, every column sum $\sum_{i=0}^2 (S(i,j)+1) = 15$, the main diagonal sum $\sum_{i=0}^2 (S(i,i)+1) = 15$, and the anti-diagonal sum $\sum_{i=0}^2 (S(i, 2-i)+1) = 15$.
-/

/-- Magic square predicate for an order-3 arrangement. -/
def is_magic_arrangement3 (S : Fin 3 × Fin 3 ≃ Fin 9) : Prop :=
  (∀ i : Fin 3, ∑ j : Fin 3, ((S (i, j)).val + 1 : ℤ) = 15) ∧
  (∀ j : Fin 3, ∑ i : Fin 3, ((S (i, j)).val + 1 : ℤ) = 15) ∧
  (∑ i : Fin 3, ((S (i, i)).val + 1 : ℤ) = 15) ∧
  (∑ i : Fin 3, ((S (i, Fin.rev i)).val + 1 : ℤ) = 15)
