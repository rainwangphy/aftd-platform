import AFTD.Prelude
import AFTD.Kb.Tcs.LinkageOfCommonNeighbor
import AFTD.Kb.Tcs.DigraphIsKStrong
import AFTD.Kb.Tcs.DigraphIsDirectedPath

/-!
# linkage_of_common_neighbor_right

Topic: graphs   Node: f7ca358f18c9

Provenance: helper lemma. step towards digraph_four_strong_semicomplete_multipartite_nonadjacent_pairs_linked

In a 4-strong digraph D, if v is outside {s₁, t₁, s₂, t₂} and (s₂ → v → t₂) or (t₂ → v → s₂), then unilateral 2-linkage exists for {s₁, t₁} and {s₂, t₂}.
-/

/-- In a 4-strong digraph D, if v is outside {s₁, t₁, s₂, t₂} and (s₂ → v → t₂) or (t₂ → v → s₂), then unilateral 2-linkage exists for {s₁, t₁} and {s₂, t₂}. -/
theorem linkage_of_common_neighbor_right
    {V : Type*} [Fintype V] (D : Digraph V)
    (hstrong : digraph_is_k_strong D 4)
    {s₁ t₁ s₂ t₂ : V} (hnodup : [s₁, t₁, s₂, t₂].Nodup)
    (v : V) (hv : v ∉ [s₁, t₁, s₂, t₂])
    (hdir : (D.Adj s₂ v ∧ D.Adj v t₂) ∨ (D.Adj t₂ v ∧ D.Adj v s₂)) :
    ∃ (p₁ p₂ : List V),
      (digraph_is_directed_path D p₁ s₁ t₁ ∨ digraph_is_directed_path D p₁ t₁ s₁) ∧
      (digraph_is_directed_path D p₂ s₂ t₂ ∨ digraph_is_directed_path D p₂ t₂ s₂) ∧
      p₁.Disjoint p₂ := by
  have hnodup' : [s₂, t₂, s₁, t₁].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
      List.nodup_nil, and_true] at hnodup ⊢
    tauto
  have hv' : v ∉ [s₂, t₂, s₁, t₁] := by
    simp only [List.mem_cons, List.not_mem_nil] at hv ⊢
    tauto
  obtain ⟨p₁, p₂, ⟨h₁, h₂, hd⟩⟩ :=
    linkage_of_common_neighbor D hstrong hnodup' v hv' hdir
  exact ⟨p₂, p₁, h₂, h₁, hd.symm⟩
