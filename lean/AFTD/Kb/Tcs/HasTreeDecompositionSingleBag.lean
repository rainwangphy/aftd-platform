import AFTD.Prelude
import AFTD.Kb.Tcs.HasTreeDecompositionOfWidthLe

/-!
# has_tree_decomposition_single_bag

Topic: proof_complexity   Node: 3912356379fa

Sanity check: every finite graph has a tree decomposition of width at most (number of vertices - 1), the one-node tree whose bag is every vertex; so treewidth is well defined on finite graphs.
-/

theorem has_tree_decomposition_single_bag {α : Type*} [Fintype α] (G : SimpleGraph α) : has_tree_decomposition_of_width_le G (Fintype.card α - 1) := by
  classical
  refine ⟨1, ⊥, fun _ => Finset.univ, ?_, fun v => ⟨0, Finset.mem_univ v⟩,
    fun u v _ => ⟨0, Finset.mem_univ u, Finset.mem_univ v⟩, ?_, fun _ => ?_⟩
  · refine ⟨⟨fun u v => ?_⟩, SimpleGraph.isAcyclic_bot⟩
    obtain rfl := Subsingleton.elim u v
    exact SimpleGraph.Reachable.refl u
  · intro v
    haveI : Nonempty ({t | v ∈ (Finset.univ : Finset α)} : Set (Fin 1)) :=
      ⟨⟨0, Finset.mem_univ v⟩⟩
    refine ⟨fun u w => ?_⟩
    obtain rfl := Subsingleton.elim u w
    exact SimpleGraph.Reachable.refl u
  · simp only [Finset.card_univ]
    omega
