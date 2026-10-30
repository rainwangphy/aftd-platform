import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphFourStrongSemicompleteMultipartiteAdjacentPairLinked
import AFTD.Kb.Tcs.DigraphIsSemicompleteMultipartite
import AFTD.Kb.Tcs.DigraphIsKStrong
import AFTD.Kb.Tcs.DigraphIsDirectedPath

/-!
# digraph_four_strong_semicomplete_multipartite_adjacent_pair_linked_right

Topic: graphs   Node: 9f7fd9917788

Provenance: helper lemma. step towards op_620_four_strong_semicomplete_multipartite_unilaterally_two_linked

Let D be a 4-strong semicomplete multipartite digraph. If s₁, t₁, s₂, t₂ are pairwise distinct vertices such that there is an arc between s₂ and t₂ in either direction, then there exist vertex-disjoint directed paths p₁ and p₂ linking {s₁, t₁} and {s₂, t₂} unilaterally.
-/

/-- In a 4-strong semicomplete multipartite digraph, if the second terminal pair is adjacent, unilateral 2-linkage exists. -/
theorem digraph_four_strong_semicomplete_multipartite_adjacent_pair_linked_right
    {V : Type*} [Fintype V] (D : Digraph V)
    (hstrong : digraph_is_k_strong D 4)
    (hmulti : digraph_is_semicomplete_multipartite D)
    {s₁ t₁ s₂ t₂ : V} (hnodup : [s₁, t₁, s₂, t₂].Nodup)
    (hadj : D.Adj s₂ t₂ ∨ D.Adj t₂ s₂) :
    ∃ (p₁ p₂ : List V),
      (digraph_is_directed_path D p₁ s₁ t₁ ∨ digraph_is_directed_path D p₁ t₁ s₁) ∧
      (digraph_is_directed_path D p₂ s₂ t₂ ∨ digraph_is_directed_path D p₂ t₂ s₂) ∧
      p₁.Disjoint p₂ := by
  have hnodup' : [s₂, t₂, s₁, t₁].Nodup := by
    have h' := hnodup
    simp only [List.nodup_cons] at h'
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at h'
    simp only [List.nodup_cons]
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true]
    tauto
  obtain ⟨q₁, q₂, hq₁, hq₂, hdisj⟩ :=
    digraph_four_strong_semicomplete_multipartite_adjacent_pair_linked D hstrong hmulti hnodup' hadj
  exact ⟨q₂, q₁, hq₂, hq₁, hdisj.symm⟩
