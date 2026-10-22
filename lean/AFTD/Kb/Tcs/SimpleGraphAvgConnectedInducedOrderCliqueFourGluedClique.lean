import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphAvgConnectedInducedOrder
import AFTD.Kb.Tcs.SimpleGraphCliqueFourGluedClique
import AFTD.Kb.Tcs.SimpleGraphCliqueFourGluedCliqueConnectedCardAndSum

/-!
# simple_graph_avg_connected_induced_order_clique_four_glued_clique

Topic: graphs   Node: f08890d4f245

Provenance: helper lemma. evaluation of A(G) on the conjectured extremal graph of OP-444; serves simple_graph_avg_connected_induced_order_min_cut_vertex_no_bridge

For n ≥ 7, A(K_4 ·_v K_{n−3}) = (12 + (n−4)2^{n−5} + 2^{n−1} + (n−1)2^{n−2}) / (2^{n−4} + 2^{n−1} + 6): the connected vertex sets are the nonempty subsets of one clique minus the shared vertex, and all sets containing the shared vertex.
-/

/-- Two `Finset.filter`s of the same predicate differ only in their decidability instance. -/
theorem simple_graph_avg_connected_induced_order_clique_four_glued_clique_filter_congr
    {α : Type*} (p : α → Prop) (h1 h2 : DecidablePred p) (s : Finset α) :
    @Finset.filter α p h1 s = @Finset.filter α p h2 s := by
  ext x
  simp only [Finset.mem_filter]

theorem simple_graph_avg_connected_induced_order_clique_four_glued_clique (n : ℕ) (hn : 7 ≤ n) :
    simple_graph_avg_connected_induced_order (simple_graph_clique_four_glued_clique n) =
      ((12 + (n - 4) * 2 ^ (n - 5) + 2 ^ (n - 1) + (n - 1) * 2 ^ (n - 2) : ℕ) : ℚ) /
        ((2 ^ (n - 4) + 2 ^ (n - 1) + 6 : ℕ) : ℚ) := by
  obtain ⟨h1, h2⟩ := simple_graph_clique_four_glued_clique_connected_card_and_sum n hn
  simp only [simple_graph_avg_connected_induced_order]
  rw [simple_graph_avg_connected_induced_order_clique_four_glued_clique_filter_congr
    (fun S : Finset (Fin n) =>
      (SimpleGraph.induce (S : Set (Fin n)) (simple_graph_clique_four_glued_clique n)).Connected)
    _ (fun x => Classical.dec _)]
  rw [h2, h1]
