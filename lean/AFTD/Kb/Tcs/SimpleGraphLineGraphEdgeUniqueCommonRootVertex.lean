import AFTD.Prelude

/-!
# simple_graph_line_graph_edge_unique_common_root_vertex

Topic: graphs   Node: 1788735a2f0a

Provenance: helper lemma. Star-clique edge partition for the line-graph cover route.

Every edge of the line graph of a simple graph is contained in a unique star clique of the root graph: its two distinct root edges have a unique common endpoint.
-/

theorem simple_graph_line_graph_edge_unique_common_root_vertex
    (n : ℕ) (H : SimpleGraph (Fin n)) (e : Sym2 H.edgeSet)
    (he : e ∈ H.lineGraph.edgeSet) :
    ∃! v : Fin n, ∀ f ∈ e, v ∈ f.val := by
  classical
  induction e using Sym2.ind with
  | h a b =>
    have hadj : H.lineGraph.Adj a b := (SimpleGraph.mem_edgeSet _).mp he
    obtain ⟨hab, v, hva, hvb⟩ := SimpleGraph.lineGraph_adj_iff_exists.mp hadj
    refine ⟨v, ?_, ?_⟩
    · intro f hf
      rw [Sym2.mem_iff] at hf
      rcases hf with rfl | rfl <;> assumption
    · intro w hw
      have hwa : w ∈ a.val := hw a (by simp)
      have hwb : w ∈ b.val := hw b (by simp)
      by_contra hne
      have E1 : a.val = s(w, v) := (Sym2.mem_and_mem_iff hne).mp ⟨hwa, hva⟩
      have E2 : b.val = s(w, v) := (Sym2.mem_and_mem_iff hne).mp ⟨hwb, hvb⟩
      exact hab (Subtype.ext (E1.trans E2.symm))
