import AFTD.Prelude

/-!
# vertex_disjoint_routing_exists

Topic: approximation   Node: 433a5818b4ac

Provenance: helper lemma. step towards weighted_spanning_tree_congestion_hardness_gap

`DisjointPathsExist`: there is a tuple of paths in `Q`, the `i`-th joining `s_i` to `t_i`, whose supports are pairwise disjoint.
-/

/-- The disjoint-paths predicate: the `s_i`--`t_i` pairs can be joined by pairwise vertex-disjoint paths in `Q`. -/
def vertex_disjoint_routing_exists {V : Type*} (Q : SimpleGraph V) {p : ℕ} (s t : Fin p → V) : Prop := ∃ P : (i : Fin p) → Q.Walk (s i) (t i),
    (∀ i, (P i).IsPath) ∧ ∀ i j, i ≠ j → (P i).support.Disjoint (P j).support
