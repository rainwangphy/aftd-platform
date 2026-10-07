import AFTD.Prelude
import AFTD.Kb.Tcs.GraphMatchingNum

/-!
# graph_matching_num_two_mul_le_card

Topic: graphs   Node: a26caafd9896

Provenance: helper lemma. folklore

In any finite simple graph G on vertex set V, twice the matching number is at most the number of vertices, 2 * graph_matching_num G ≤ |V|.
-/

lemma graph_matching_num_two_mul_le_card_endpoints_of_mem_edgeSet {V : Type*} {G : SimpleGraph V}
    (M : G.Subgraph) (e : M.edgeSet) :
    ∃ p : V × V, e.1 = s(p.1, p.2) ∧ M.Adj p.1 p.2 := by
  obtain ⟨e_val, he⟩ := e
  induction e_val using Sym2.ind with
  | h u v =>
    exact ⟨(u, v), rfl, he⟩

noncomputable def graph_matching_num_two_mul_le_card_edgeEndpoints {V : Type*} {G : SimpleGraph V}
    (M : G.Subgraph) (e : M.edgeSet) : V × V :=
  Classical.choose (graph_matching_num_two_mul_le_card_endpoints_of_mem_edgeSet M e)

lemma graph_matching_num_two_mul_le_card_edgeEndpoints_spec {V : Type*} {G : SimpleGraph V}
    (M : G.Subgraph) (e : M.edgeSet) :
    e.1 = s((graph_matching_num_two_mul_le_card_edgeEndpoints M e).1, (graph_matching_num_two_mul_le_card_edgeEndpoints M e).2) ∧
    M.Adj (graph_matching_num_two_mul_le_card_edgeEndpoints M e).1 (graph_matching_num_two_mul_le_card_edgeEndpoints M e).2 :=
  Classical.choose_spec (graph_matching_num_two_mul_le_card_endpoints_of_mem_edgeSet M e)

lemma graph_matching_num_two_mul_le_card_toEdge_endpoint1 {V : Type*} {G : SimpleGraph V}
    {M : G.Subgraph} (hM : M.IsMatching) (e : M.edgeSet) :
    hM.toEdge ⟨(graph_matching_num_two_mul_le_card_edgeEndpoints M e).1,
      (graph_matching_num_two_mul_le_card_edgeEndpoints_spec M e).2.fst_mem⟩ = e := by
  have := hM.toEdge_eq_of_adj (graph_matching_num_two_mul_le_card_edgeEndpoints_spec M e).2
  apply Subtype.ext
  have h_val := congr_arg Subtype.val this
  exact h_val.trans (graph_matching_num_two_mul_le_card_edgeEndpoints_spec M e).1.symm

lemma graph_matching_num_two_mul_le_card_toEdge_endpoint2 {V : Type*} {G : SimpleGraph V}
    {M : G.Subgraph} (hM : M.IsMatching) (e : M.edgeSet) :
    hM.toEdge ⟨(graph_matching_num_two_mul_le_card_edgeEndpoints M e).2,
      (graph_matching_num_two_mul_le_card_edgeEndpoints_spec M e).2.snd_mem⟩ = e := by
  have := hM.toEdge_eq_of_adj (graph_matching_num_two_mul_le_card_edgeEndpoints_spec M e).2.symm
  apply Subtype.ext
  have h_val := congr_arg Subtype.val this
  exact h_val.trans (Sym2.eq_swap.trans (graph_matching_num_two_mul_le_card_edgeEndpoints_spec M e).1.symm)

noncomputable def graph_matching_num_two_mul_le_card_endpoint {V : Type*} {G : SimpleGraph V}
    (M : G.Subgraph) (p : Fin 2 × M.edgeSet) : V :=
  if p.1 = 0 then (graph_matching_num_two_mul_le_card_edgeEndpoints M p.2).1
  else (graph_matching_num_two_mul_le_card_edgeEndpoints M p.2).2

lemma graph_matching_num_two_mul_le_card_endpoint_mem_verts {V : Type*} {G : SimpleGraph V}
    (M : G.Subgraph) (p : Fin 2 × M.edgeSet) :
    graph_matching_num_two_mul_le_card_endpoint M p ∈ M.verts := by
  dsimp [graph_matching_num_two_mul_le_card_endpoint]
  split_ifs
  · exact (graph_matching_num_two_mul_le_card_edgeEndpoints_spec M p.2).2.fst_mem
  · exact (graph_matching_num_two_mul_le_card_edgeEndpoints_spec M p.2).2.snd_mem

lemma graph_matching_num_two_mul_le_card_toEdge_endpoint {V : Type*} {G : SimpleGraph V}
    {M : G.Subgraph} (hM : M.IsMatching) (p : Fin 2 × M.edgeSet) :
    hM.toEdge ⟨graph_matching_num_two_mul_le_card_endpoint M p,
      graph_matching_num_two_mul_le_card_endpoint_mem_verts M p⟩ = p.2 := by
  dsimp [graph_matching_num_two_mul_le_card_endpoint]
  split_ifs
  · exact graph_matching_num_two_mul_le_card_toEdge_endpoint1 hM p.2
  · exact graph_matching_num_two_mul_le_card_toEdge_endpoint2 hM p.2

lemma graph_matching_num_two_mul_le_card_fin2_ne_cases {i j : Fin 2} (h : i ≠ j) :
    (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by
  revert i j
  decide

lemma graph_matching_num_two_mul_le_card_endpoint_injective {V : Type*} {G : SimpleGraph V}
    {M : G.Subgraph} (hM : M.IsMatching) :
    Function.Injective (graph_matching_num_two_mul_le_card_endpoint M) := by
  intro p₁ p₂ h
  have he : p₁.2 = p₂.2 := by
    have h1 := graph_matching_num_two_mul_le_card_toEdge_endpoint hM p₁
    have h2 := graph_matching_num_two_mul_le_card_toEdge_endpoint hM p₂
    have h_eq : (⟨graph_matching_num_two_mul_le_card_endpoint M p₁,
                   graph_matching_num_two_mul_le_card_endpoint_mem_verts M p₁⟩ : M.verts) =
                ⟨graph_matching_num_two_mul_le_card_endpoint M p₂,
                 graph_matching_num_two_mul_le_card_endpoint_mem_verts M p₂⟩ := Subtype.ext h
    rw [h_eq] at h1
    exact h1.symm.trans h2
  have hi : p₁.1 = p₂.1 := by
    by_contra hne
    rcases graph_matching_num_two_mul_le_card_fin2_ne_cases hne with ⟨h0, h1⟩ | ⟨h1, h0⟩
    · exfalso
      have hp1 : graph_matching_num_two_mul_le_card_endpoint M p₁ =
          (graph_matching_num_two_mul_le_card_edgeEndpoints M p₁.2).1 := by
        dsimp [graph_matching_num_two_mul_le_card_endpoint]
        rw [if_pos h0]
      have hp2 : graph_matching_num_two_mul_le_card_endpoint M p₂ =
          (graph_matching_num_two_mul_le_card_edgeEndpoints M p₂.2).2 := by
        dsimp [graph_matching_num_two_mul_le_card_endpoint]
        rw [if_neg (by rw [h1]; decide)]
      rw [hp1, hp2, he] at h
      exact (graph_matching_num_two_mul_le_card_edgeEndpoints_spec M p₂.2).2.ne h
    · exfalso
      have hp1 : graph_matching_num_two_mul_le_card_endpoint M p₁ =
          (graph_matching_num_two_mul_le_card_edgeEndpoints M p₁.2).2 := by
        dsimp [graph_matching_num_two_mul_le_card_endpoint]
        rw [if_neg (by rw [h1]; decide)]
      have hp2 : graph_matching_num_two_mul_le_card_endpoint M p₂ =
          (graph_matching_num_two_mul_le_card_edgeEndpoints M p₂.2).1 := by
        dsimp [graph_matching_num_two_mul_le_card_endpoint]
        rw [if_pos h0]
      rw [hp1, hp2, he] at h
      exact (graph_matching_num_two_mul_le_card_edgeEndpoints_spec M p₂.2).2.symm.ne h
  exact Prod.ext hi he

/-- Twice the matching number is at most the number of vertices in a finite graph. -/
theorem graph_matching_num_two_mul_le_card {V : Type*} [Fintype V] (G : SimpleGraph V) :
    2 * graph_matching_num G ≤ (Fintype.card V : ℕ∞) := by
  dsimp [graph_matching_num]
  rw [ENat.mul_iSup]
  refine iSup_le fun M ↦ ?_
  rw [ENat.mul_iSup]
  refine iSup_le fun hM ↦ ?_
  have hinj := graph_matching_num_two_mul_le_card_endpoint_injective hM
  have hcard := ENat.card_le_card_of_injective hinj
  have hprod : ENat.card (Fin 2 × M.edgeSet) = 2 * M.edgeSet.encard := by
    rw [ENat.card_prod, ENat.card_coe_set_eq]
    simp
  rw [ENat.card_eq_coe_fintype_card (α := V)] at hcard
  exact hprod ▸ hcard
