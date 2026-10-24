import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphIsOriented
import AFTD.Kb.Tcs.DigraphHasIsolatedEdge

/-!
# digraph_has_isolated_edge_card_ge_two

Topic: graphs   Node: c96747053300

Provenance: helper lemma. folklore

If a finite oriented digraph G : Digraph V satisfies digraph_has_isolated_edge G and digraph_is_oriented G, then Fintype.card V ≥ 2.
-/

/-- An oriented graph with an isolated edge has at least two vertices. -/
theorem digraph_has_isolated_edge_card_ge_two {V : Type*} [Fintype V] {G : Digraph V} (hG : digraph_is_oriented G) (h : digraph_has_isolated_edge G) : 2 ≤ Fintype.card V := by
  obtain ⟨u, v, huv, -⟩ := h
  have hne : u ≠ v := by
    intro heq
    subst v
    exact (hG u u huv) huv
  have hlt : 1 < Fintype.card V := (Fintype.one_lt_card_iff).2 ⟨u, v, hne⟩
  omega
