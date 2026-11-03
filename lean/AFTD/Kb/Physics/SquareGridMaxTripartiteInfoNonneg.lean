import AFTD.Prelude
import AFTD.Kb.Physics.SquareGridGraphMaxTripartiteInfo
import AFTD.Kb.Physics.SquareGridGraphTripartiteInfo
import AFTD.Kb.Physics.TreeGraphStateTripartiteInfo
import AFTD.Kb.Physics.TreeGraphStateTripartiteInfoTrivialZero

/-!
# square_grid_max_tripartite_info_nonneg

Topic: quantum_mechanics   Node: 177af27a1454

Provenance: formalization of a published result. Source: arXiv:2511.19585 ("Monogamy of Mutual Information in Graph States")

For every natural number n, the maximum tripartite information square_grid_graph_max_tripartite_info n of the n-by-n square grid graph state is at least 0.
-/

/-- The maximum tripartite information of the n-by-n square grid graph state is nonnegative for every n. -/
theorem square_grid_max_tripartite_info_nonneg (n : ℕ) :
    0 ≤ square_grid_graph_max_tripartite_info n := by
  unfold square_grid_graph_max_tripartite_info
  have hval : square_grid_graph_tripartite_info n (fun _ => (0:Fin 4)) = 0 := by
    unfold square_grid_graph_tripartite_info
    have h1 : (Finset.univ : Finset (Fin n × Fin n)).filter (fun v => (fun _ => (0:Fin 4)) v = (0:Fin 4)) = Finset.univ := by
      ext v; simp
    have h2 : (Finset.univ : Finset (Fin n × Fin n)).filter (fun v => (fun _ => (0:Fin 4)) v = (1:Fin 4)) = ∅ := by
      ext v; simp
    have h3 : (Finset.univ : Finset (Fin n × Fin n)).filter (fun v => (fun _ => (0:Fin 4)) v = (2:Fin 4)) = ∅ := by
      ext v; simp
    have h4 : (Finset.univ : Finset (Fin n × Fin n)).filter (fun v => (fun _ => (0:Fin 4)) v = (3:Fin 4)) = ∅ := by
      ext v; simp
    rw [h1, h2, h3, h4]
    exact @tree_graph_state_tripartite_info_trivial_zero (Fin n × Fin n) _ _ (SimpleGraph.pathGraph n □ SimpleGraph.pathGraph n) (Classical.decRel _)
  rw [← hval]
  exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨fun _ => (0:Fin 4), Finset.mem_univ _, rfl⟩)
