import AFTD.Prelude
import AFTD.Kb.Tcs.ShortPathGivesLinkageFourStrong
import AFTD.Kb.Tcs.DigraphIsDirectedPath
import AFTD.Kb.Tcs.DigraphIsKStrong

/-!
# linkage_of_common_neighbor

Topic: graphs   Node: 1faa361d4063

Provenance: helper lemma. step towards op_620_four_strong_semicomplete_multipartite_unilaterally_two_linked

In a 4-strong digraph D, if v is outside {s₁, t₁, s₂, t₂} and (s₁ → v → t₁) or (t₁ → v → s₁), then unilateral 2-linkage exists for {s₁, t₁} and {s₂, t₂}.
-/

/-- If an outside vertex forms a 2-step directed path between {s₁, t₁}, then unilateral 2-linkage exists in a 4-strong digraph. -/
theorem linkage_of_common_neighbor
    {V : Type*} [Fintype V] (D : Digraph V)
    (hstrong : digraph_is_k_strong D 4)
    {s₁ t₁ s₂ t₂ : V} (hnodup : [s₁, t₁, s₂, t₂].Nodup)
    (v : V) (hv : v ∉ [s₁, t₁, s₂, t₂])
    (hdir : (D.Adj s₁ v ∧ D.Adj v t₁) ∨ (D.Adj t₁ v ∧ D.Adj v s₁)) :
    ∃ (p₁ p₂ : List V),
      (digraph_is_directed_path D p₁ s₁ t₁ ∨ digraph_is_directed_path D p₁ t₁ s₁) ∧
      (digraph_is_directed_path D p₂ s₂ t₂ ∨ digraph_is_directed_path D p₂ t₂ s₂) ∧
      p₁.Disjoint p₂ := by
  have h_nodup_simped := hnodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true] at h_nodup_simped hv
  cases hdir with
  | inl h =>
    have hpath : digraph_is_directed_path D [s₁, v, t₁] s₁ t₁ := by
      refine ⟨by simp [h.1, h.2], ?_, rfl, rfl⟩
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true]
      tauto
    apply short_path_gives_linkage_four_strong D hstrong hnodup [s₁, v, t₁] (Or.inl hpath) le_rfl
    simp only [List.mem_cons, List.not_mem_nil]
    tauto
  | inr h =>
    have hpath : digraph_is_directed_path D [t₁, v, s₁] t₁ s₁ := by
      refine ⟨by simp [h.1, h.2], ?_, rfl, rfl⟩
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true]
      tauto
    apply short_path_gives_linkage_four_strong D hstrong hnodup [t₁, v, s₁] (Or.inr hpath) le_rfl
    simp only [List.mem_cons, List.not_mem_nil]
    tauto
