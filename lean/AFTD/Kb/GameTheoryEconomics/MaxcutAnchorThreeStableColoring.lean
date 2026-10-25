import AFTD.Prelude

/-!
# maxcut_anchor_three_stable_coloring

Topic: equilibria   Node: 83dbf6291231

Provenance: formalization of a published result. Source: arXiv:2610.04948 Sec. 2, displayed coloring tau after the profitable core deviation, specialized to k=3 and shifted to zero-based colors. Its stability is separately checked here. Sanity checks are maxcut_anchor_three_sanity and maxcut_anchor_three_equal_welfare_deviation.

The paper’s displayed post-deviation coloring on G_3: A has color 2, B color 0, C and D color 1, and anchor class j has color j, using zero-based colors.
-/

def maxcut_anchor_three_stable_coloring : (Fin 16 ⊕ (Fin 3 × Fin 25)) → Fin 3 :=fun v => match v with
  | .inl u => if u.val < 4 then 2 else if u.val < 8 then 0 else 1
  | .inr (j, _) => j
