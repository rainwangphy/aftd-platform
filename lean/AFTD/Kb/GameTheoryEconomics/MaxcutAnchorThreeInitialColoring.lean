import AFTD.Prelude

/-!
# maxcut_anchor_three_initial_coloring

Topic: equilibria   Node: f9fd0654bde5

Provenance: formalization of a published result. Source: arXiv:2610.04948 Sec. 2, initial displayed coloring sigma specialized to k=3, with zero-based colors and indices. The pinned-twin deviation theorem is also a sanity check of this coloring.

The initial coloring sigma of the paper graph G_3: A and D have color 0, B color 1, C color 2, and anchor class j has color j.
-/

def maxcut_anchor_three_initial_coloring : (Fin 16 ⊕ (Fin 3 × Fin 25)) → Fin 3 :=fun v => match v with
  | .inl u => if u.val < 4 then 0 else if u.val < 8 then 1 else if u.val < 12 then 2 else 0
  | .inr (j, _) => j
