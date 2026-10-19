import AFTD.Prelude
import AFTD.Kb.Tcs.IsSustainableTree
import AFTD.Kb.Tcs.IsSustainableEdge
import AFTD.Kb.Tcs.AdjacencySpectralRadius

/-!
# not_op223_path_is_sustainable

Topic: graphs   Node: 7047af61a520

Provenance: original. Related work: refutes `op223_path_is_sustainable`

The statement `op223_path_is_sustainable` is false: The statement fails at n = 2. `SimpleGraph.pathGraph 2 = SimpleGraph.hasse (Fin 2)` is the graph with the single edge `s(0,1)` on `Fin 2`. By `is_sustainable_tree T = T.IsTree ∧ ∀ e ∈ T.edgeSet, is_sustainable_edge T e`, and `is_sustainable_edge T e` requires the existence of a non-edge `f ∈ Tᶜ.edgeSet`, the unique edge of `pathGraph 2` would need a non-edge; but the complement of the single edge on `Fin 2` is the empty graph, so `(pathGraph 2)ᶜ.edgeSet = ∅`. Hence no edge of `pathGraph 2` is sustainable and `is_sustainable_tree (pathGraph 2)` is false. (For n = 1 the condition is vacuous, so n = 2 is the only failure among n ≥ 1. The knowledge base already contains the stated lemma `no_sustainable_tree_fin_two`, which is exactly this obstruction.) The statement should carry the hypothesis 3 ≤ n (or n ≠ 2).
-/

theorem not_op223_path_is_sustainable : ¬ (∀ (n : ℕ) (_hn : 1 ≤ n), is_sustainable_tree (SimpleGraph.pathGraph n)) := by
  intro h
  have hh : is_sustainable_tree (SimpleGraph.pathGraph 2) := h 2 (by norm_num)
  have h2 := hh.2
  have he : s(0,1) ∈ (SimpleGraph.pathGraph 2).edgeSet := by
    rw [SimpleGraph.mem_edgeSet]
    simp [SimpleGraph.pathGraph, SimpleGraph.hasse]
  rcases h2 (s(0,1)) he with ⟨_, f, hf, _⟩
  have hempty : (SimpleGraph.pathGraph 2)ᶜ.edgeSet = ∅ := by
    rw [SimpleGraph.edgeSet_eq_empty]
    ext a b
    rw [SimpleGraph.compl_adj]
    simp only [SimpleGraph.bot_adj, iff_false, not_and, not_not]
    intro h
    fin_cases a <;> fin_cases b <;> simp_all [SimpleGraph.pathGraph, SimpleGraph.hasse]
  rw [hempty] at hf
  exact hf
