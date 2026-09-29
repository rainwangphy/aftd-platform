import AFTD.Prelude
import AFTD.Kb.Tcs.GraphMatchingNum

/-!
# graph_matching_encard_le_vertex_cover_encard

Topic: graphs   Node: 2b71fe52b2d1

For any matching M and any vertex cover c of a simple graph G, the number of edges in M is at most the number of vertices in c.
-/

lemma graph_matching_encard_le_vertex_cover_encard_exists {V : Type*} {G : SimpleGraph V}
    {M : SimpleGraph.Subgraph G} {c : Set V} (hc : G.IsVertexCover c) (e : M.edgeSet) :
    ∃ v ∈ c, v ∈ e.val := by
  obtain ⟨e, he⟩ := e
  induction' e using Sym2.ind with u v
  rw [SimpleGraph.Subgraph.mem_edgeSet] at he
  have hadj : G.Adj u v := M.adj_sub he
  rcases hc hadj with hu | hv
  · exact ⟨u, hu, Sym2.mem_mk_left u v⟩
  · exact ⟨v, hv, Sym2.mem_mk_right u v⟩

lemma graph_matching_encard_le_vertex_cover_encard_eq_of_mem {V : Type*} {G : SimpleGraph V}
    {M : SimpleGraph.Subgraph G} (hM : M.IsMatching) {e₁ e₂ : Sym2 V}
    (h₁ : e₁ ∈ M.edgeSet) (h₂ : e₂ ∈ M.edgeSet) {v : V}
    (hv₁ : v ∈ e₁) (hv₂ : v ∈ e₂) : e₁ = e₂ := by
  induction' e₁ using Sym2.ind with u₁ w₁
  induction' e₂ using Sym2.ind with u₂ w₂
  rw [SimpleGraph.Subgraph.mem_edgeSet] at h₁ h₂
  rcases Sym2.mem_iff.mp hv₁ with rfl | rfl <;>
  rcases Sym2.mem_iff.mp hv₂ with rfl | rfl
  · have h_eq := hM.eq_of_adj_left h₁ h₂
    rw [h_eq]
  · have h_eq := hM.eq_of_adj_left h₁ h₂.symm
    rw [h_eq, Sym2.eq_swap]
  · have h_eq := hM.eq_of_adj_left h₁.symm h₂
    rw [h_eq, Sym2.eq_swap]
  · have h_eq := hM.eq_of_adj_left h₁.symm h₂.symm
    rw [h_eq]

/-- The cardinality of edges in any matching is at most the cardinality of any vertex cover. -/
theorem graph_matching_encard_le_vertex_cover_encard {V : Type*} (G : SimpleGraph V) (M : SimpleGraph.Subgraph G) (c : Set V) (hM : M.IsMatching) (hc : G.IsVertexCover c) : M.edgeSet.encard ≤ c.encard := by
  let f : M.edgeSet → c := fun e ↦
    ⟨Classical.choose (graph_matching_encard_le_vertex_cover_encard_exists hc e),
     (Classical.choose_spec (graph_matching_encard_le_vertex_cover_encard_exists hc e)).1⟩
  have hf : Function.Injective f := by
    intro e₁ e₂ h
    have h_val : Classical.choose (graph_matching_encard_le_vertex_cover_encard_exists hc e₁) =
                 Classical.choose (graph_matching_encard_le_vertex_cover_encard_exists hc e₂) :=
      congr_arg Subtype.val h
    have hv₁ := (Classical.choose_spec (graph_matching_encard_le_vertex_cover_encard_exists hc e₁)).2
    have hv₂ := (Classical.choose_spec (graph_matching_encard_le_vertex_cover_encard_exists hc e₂)).2
    rw [h_val] at hv₁
    exact Subtype.ext (graph_matching_encard_le_vertex_cover_encard_eq_of_mem hM e₁.2 e₂.2 hv₁ hv₂)
  exact ENat.card_le_card_of_injective hf
