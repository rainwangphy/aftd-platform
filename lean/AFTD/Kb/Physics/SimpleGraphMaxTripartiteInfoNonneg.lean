import AFTD.Prelude
import AFTD.Kb.Physics.SimpleGraphMaxTripartiteInfo
import AFTD.Kb.Physics.TreeGraphStateTripartiteInfoTrivialZero
import AFTD.Kb.Physics.TreeGraphStateTripartiteInfo

/-!
# simple_graph_max_tripartite_info_nonneg

Topic: quantum_mechanics   Node: c570f0869173

Provenance: helper lemma. arXiv:2511.19585

For every finite simple graph G, the maximum tripartite information simple_graph_max_tripartite_info G is at least 0, witnessed by the constant four-coloring with three empty parts.
-/

/-- The maximum tripartite information of any finite graph state is nonnegative. -/
theorem simple_graph_max_tripartite_info_nonneg
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    0 ≤ simple_graph_max_tripartite_info G := by
  let f : (V → Fin 4) → ℤ := fun c =>
    tree_graph_state_tripartite_info G
      (Finset.univ.filter (fun v => c v = 0))
      (Finset.univ.filter (fun v => c v = 1))
      (Finset.univ.filter (fun v => c v = 2))
      (Finset.univ.filter (fun v => c v = 3))
  have h1 : (Finset.univ : Finset V).filter (fun v => (fun (_ : V) => (0:Fin 4)) v = (0:Fin 4)) = Finset.univ := by
    ext v; simp
  have h2 : (Finset.univ : Finset V).filter (fun v => (fun (_ : V) => (0:Fin 4)) v = (1:Fin 4)) = ∅ := by
    ext v; simp
  have h3 : (Finset.univ : Finset V).filter (fun v => (fun (_ : V) => (0:Fin 4)) v = (2:Fin 4)) = ∅ := by
    ext v; simp
  have h4 : (Finset.univ : Finset V).filter (fun v => (fun (_ : V) => (0:Fin 4)) v = (3:Fin 4)) = ∅ := by
    ext v; simp
  have hval : f (fun _ => 0) = 0 := by
    change tree_graph_state_tripartite_info G _ _ _ _ = 0
    rw [h1, h2, h3, h4]
    exact tree_graph_state_tripartite_info_trivial_zero G
  unfold simple_graph_max_tripartite_info
  change 0 ≤ (((Finset.univ : Finset (V → Fin 4)).image f).max' _)
  rw [← hval]
  exact Finset.le_max' _ (f (fun _ => 0)) (Finset.mem_image_of_mem f (Finset.mem_univ _))
