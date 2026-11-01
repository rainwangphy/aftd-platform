import AFTD.Prelude

/-!
# arrangement3_entry

Topic: combinatorics   Node: f21791863f04

Provenance: formalization of a published result. Source: arXiv:2610.38386, Section 2.1

The entry $s_{ij}$ at cell $(i, j)$ of an arrangement $S : \mathrm{Fin}\,3 \times \mathrm{Fin}\,3 \simeq \mathrm{Fin}\,9$, defined by adding $1$ to the natural number value of $S(i, j)$, yielding an integer in $\{1, \dots, 9\}$.
-/

/-- The integer entry in {1, ..., 9} at cell (i, j) of an order-3 arrangement. -/
def arrangement3_entry (S : Fin 3 × Fin 3 ≃ Fin 9) (i j : Fin 3) : ℤ := (S (i, j)).val + 1
