import AFTD.Prelude

/-!
# maxcut_anchor_three_graph

Topic: equilibria   Node: c35fb4d8fa88

Provenance: formalization of a published result. Source: arXiv:2610.04948 Sec. 2, graph G_k specialized to k=3. Core vertices 0..3,4..7,8..11,12..15 represent A,B,C,D. Anchor vertex (j,i) represents r_(j+1,i+1). The relation is symmetrized and made loopless by SimpleGraph.fromRel. Sanity checks are maxcut_anchor_three_sanity and maxcut_anchor_three_equal_welfare_deviation.

The 91-vertex graph G_3 of arXiv:2610.04948: a 16-vertex core A,B,C,D and three anchor classes of 25 vertices. Indices and colors are shifted from the paper’s one-based labels to zero-based Fin labels.
-/

namespace MaxcutAnchorThree

private def core_rel (u v : Fin 16) : Prop :=
  (u.val < 4 ∧ 12 ≤ v.val) ∨
  (u.val < 4 ∧ 4 ≤ v.val ∧ v.val < 8 ∧ u.val ≠ v.val - 4) ∨
  (4 ≤ u.val ∧ u.val < 8 ∧ 12 ≤ v.val ∧ u.val - 4 ≠ v.val - 12) ∨
  (u.val < 4 ∧ v.val = u.val + 8) ∨
  (4 ≤ u.val ∧ u.val < 8 ∧
    (v.val = u.val + 4 ∨ v.val = (u.val - 4) / 2 * 2 + (1 - (u.val - 4) % 2) + 8))

private def field (u : Fin 16) (j : Fin 3) : ℕ :=
  match u.val / 4, j.val with
  | 0, 1 => 6
  | 0, 2 => 3
  | 1, 1 => 1
  | 1, 2 => 6
  | 2, 0 => 6
  | 2, 2 => 1
  | 3, 1 => 3
  | 3, 2 => 6
  | _, _ => 0

private def rel : (Fin 16 ⊕ (Fin 3 × Fin 25)) → (Fin 16 ⊕ (Fin 3 × Fin 25)) → Prop
  | .inl u, .inl v => core_rel u v
  | .inl u, .inr (j, i) => i.val < field u j
  | .inr _, .inl _ => False
  | .inr (j, _), .inr (l, _) => j ≠ l

private instance rel_decidable : DecidableRel rel := by
  intro u v
  cases u <;> cases v <;> dsimp [rel, core_rel] <;> infer_instance

end MaxcutAnchorThree

def maxcut_anchor_three_graph : SimpleGraph (Fin 16 ⊕ (Fin 3 × Fin 25)) :=SimpleGraph.fromRel MaxcutAnchorThree.rel
