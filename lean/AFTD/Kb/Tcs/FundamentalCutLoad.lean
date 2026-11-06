import AFTD.Prelude

/-!
# fundamental_cut_load

Topic: approximation   Node: 7b5e4b4f7286

Provenance: helper lemma. step towards weighted_spanning_tree_congestion_hardness_gap

The load of the fundamental cut of an edge `e` in a spanning tree `T` of `H`: the total `w`-weight of the edges of `H` whose endpoints are separated by deleting `e` from `T`.
-/

/-- Weighted load of the fundamental cut of `e` in `T`: the sum of the weights of the `H`-edges crossing the cut induced by deleting `e` from `T`. -/
noncomputable def fundamental_cut_load {α : Type*} [Fintype α] [DecidableEq α]
    (H : SimpleGraph α) [DecidableRel H.Adj] (w : Sym2 α → ℕ)
    (T : SimpleGraph α) (e : Sym2 α) : ℕ := by
  classical
  exact ∑ uv ∈ H.edgeFinset,
    if Sym2.lift ⟨fun u v => ¬ (T.deleteEdges {e}).Reachable u v,
      fun _ _ => propext ⟨fun h hr => h hr.symm, fun h hr => h hr.symm⟩⟩ uv
    then w uv else 0
