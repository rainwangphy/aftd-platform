import AFTD.Prelude
import AFTD.Kb.Physics.TreeGraphStateTripartiteInfo

/-!
# simple_graph_max_tripartite_info

Topic: quantum_mechanics   Node: 4363c493822a

Provenance: original. Related work: arXiv:2511.19585

For any finite simple graph G with decidable equality and decidable adjacency, simple_graph_max_tripartite_info G is the maximum of tree_graph_state_tripartite_info G A B C D over all four-colorings c : V → Fin 4, taking A, B, C, D as the four color classes.
-/

/-- Maximum tripartite information of a graph state over all four-partitions of its vertices. -/
noncomputable def simple_graph_max_tripartite_info {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℤ := ((Finset.univ : Finset (V → Fin 4)).image (fun c =>
    tree_graph_state_tripartite_info G
      (Finset.univ.filter (fun v => c v = 0))
      (Finset.univ.filter (fun v => c v = 1))
      (Finset.univ.filter (fun v => c v = 2))
      (Finset.univ.filter (fun v => c v = 3)))).max' (by
    rw [Finset.image_nonempty, Finset.univ_nonempty_iff]
    exact ⟨fun _ => 0⟩)
