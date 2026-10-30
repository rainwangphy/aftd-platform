import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphIsKStrong
import AFTD.Kb.Tcs.DigraphIsDirectedPath

/-!
# short_path_gives_linkage_four_strong

Topic: graphs   Node: df205c4e3c99

Provenance: helper lemma. step towards op_620_four_strong_semicomplete_multipartite_unilaterally_two_linked

In a 4-strong digraph D, if there is a directed path between {s₁, t₁} with at most 3 vertices that avoids {s₂, t₂}, then there exist vertex-disjoint directed paths unilaterally linking {s₁, t₁} and {s₂, t₂}.
-/

/-- If there is a short directed path (at most 3 vertices) between one terminal pair avoiding the other, 4-strongness gives unilateral 2-linkage. -/
theorem short_path_gives_linkage_four_strong
    {V : Type*} [Fintype V] (D : Digraph V)
    (hstrong : digraph_is_k_strong D 4)
    {s₁ t₁ s₂ t₂ : V} (hnodup : [s₁, t₁, s₂, t₂].Nodup)
    (p₁ : List V)
    (hp₁path : digraph_is_directed_path D p₁ s₁ t₁ ∨ digraph_is_directed_path D p₁ t₁ s₁)
    (hp₁len : p₁.length ≤ 3)
    (hp₁avoid : s₂ ∉ p₁ ∧ t₂ ∉ p₁) :
    ∃ (p₁' p₂ : List V),
      (digraph_is_directed_path D p₁' s₁ t₁ ∨ digraph_is_directed_path D p₁' t₁ s₁) ∧
      (digraph_is_directed_path D p₂ s₂ t₂ ∨ digraph_is_directed_path D p₂ t₂ s₂) ∧
      p₁'.Disjoint p₂ := by
  classical
  obtain ⟨-, hstrong'⟩ := hstrong
  have hp₁nodup : p₁.Nodup := hp₁path.elim (fun h => h.2.1) (fun h => h.2.1)
  have hscard : p₁.toFinset.card < 4 := by
    rw [List.toFinset_card_of_nodup hp₁nodup]
    omega
  have hmem_s₂ : s₂ ∉ p₁.toFinset := by simpa using hp₁avoid.1
  have hmem_t₂ : t₂ ∉ p₁.toFinset := by simpa using hp₁avoid.2
  have hst : s₂ ≠ t₂ := by
    intro hh
    rw [hh] at hnodup
    simp at hnodup
  obtain ⟨p₂, hp₂path, hp₂avoid⟩ := hstrong' p₁.toFinset hscard s₂ t₂ hmem_s₂ hmem_t₂ hst
  refine ⟨p₁, p₂, hp₁path, Or.inl hp₂path, ?_⟩
  intro a ha hb
  exact hp₂avoid a hb (by simpa using ha)
