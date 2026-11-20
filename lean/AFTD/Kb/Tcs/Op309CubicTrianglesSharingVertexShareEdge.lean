import AFTD.Prelude

/-!
# op309_cubic_triangles_sharing_vertex_share_edge

Topic: graphs   Node: 4093653ea715

Provenance: helper lemma. Triangle and diamond decomposition for OP-309.

In a finite cubic simple graph, any two triangles sharing a vertex also share an edge.
-/

theorem op309_cubic_triangles_sharing_vertex_share_edge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hdegree : ∀ v, G.degree v = 3)
    (v a b c d : V)
    (ha : G.Adj v a) (hb : G.Adj v b) (hab : G.Adj a b)
    (hc : G.Adj v c) (hd : G.Adj v d) (hcd : G.Adj c d) :
    a = c ∨ a = d ∨ b = c ∨ b = d := by
  by_contra hne
  push Not at hne
  obtain ⟨h1, h2, h3, h4⟩ := hne
  have hsub : ({a, b, c, d} : Finset V) ⊆ G.neighborFinset v := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [G.mem_neighborFinset]
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have hcard : ({a, b, c, d} : Finset V).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair hcd.ne]
    · simp [h3, h4]
    · simp [hab.ne, h1, h2]
  have := Finset.card_le_card hsub
  rw [hcard, G.card_neighborFinset_eq_degree, hdegree] at this
  omega
