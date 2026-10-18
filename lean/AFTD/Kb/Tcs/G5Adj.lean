import AFTD.Prelude

/-!
# g5_adj

Topic: graphs   Node: 0c839ac7ad3f

Provenance: formalization of a published result. Source: arXiv:2610.21388 (Stronger spectral bound for clique number), Definition 2.1 with t = 5 and the vertex order fixed after it

G_5 on vertices r_1, r_2, w_1, w_2, r_3 (indices 0..4): edges r_1 r_2, w_1 w_2, r_2 w_2, and r_3 adjacent to all.
-/

/-- Adjacency of the base graph `G₅` of arXiv:2610.21388, Def. 2.1 (`t = 5`), on `Fin 5` in the paper's order `r₁, r₂, w₁, w₂, r₃`: the path `r₁ - r₂ - w₂ - w₁` plus `r₃` joined to all other vertices. -/
abbrev g5_adj (i j : Fin 5) : Prop :=
  i ≠ j ∧ (i = 4 ∨ j = 4 ∨ (i, j) ∈ ({(0, 1), (1, 0), (1, 3), (3, 1), (2, 3), (3, 2)} : Finset (Fin 5 × Fin 5)))
