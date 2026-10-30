import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphIsKStrong
import AFTD.Kb.Tcs.DigraphIsSemicompleteMultipartite
import AFTD.Kb.Tcs.DigraphIsDirectedPath

/-!
# digraph_four_strong_semicomplete_multipartite_adjacent_pair_linked

Topic: graphs   Node: 75effcde8839

Provenance: original. Related work: arXiv:2610.36895 Sec. 5

Let D be a 4-strong semicomplete multipartite digraph on a finite type V. If s₁, t₁, s₂, t₂ are pairwise distinct vertices of D such that there is an arc between s₁ and t₁ in either direction, then there exist vertex-disjoint directed paths p₁ and p₂ where p₁ connects {s₁, t₁} and p₂ connects {s₂, t₂} in either direction.
-/

/-- In a 4-strong semicomplete multipartite digraph, any two pairs of distinct terminals with one pair adjacent in either direction admit vertex-disjoint paths. -/
theorem digraph_four_strong_semicomplete_multipartite_adjacent_pair_linked
    {V : Type*} [Fintype V] (D : Digraph V)
    (hstrong : digraph_is_k_strong D 4)
    (hmulti : digraph_is_semicomplete_multipartite D)
    {s₁ t₁ s₂ t₂ : V} (hnodup : [s₁, t₁, s₂, t₂].Nodup)
    (hadj : D.Adj s₁ t₁ ∨ D.Adj t₁ s₁) :
    ∃ (p₁ p₂ : List V),
      (digraph_is_directed_path D p₁ s₁ t₁ ∨ digraph_is_directed_path D p₁ t₁ s₁) ∧
      (digraph_is_directed_path D p₂ s₂ t₂ ∨ digraph_is_directed_path D p₂ t₂ s₂) ∧
      p₁.Disjoint p₂ := by
  classical
  have h11 : s₁ ≠ t₁ := by
    intro heq
    simp [heq] at hnodup
  have h21 : s₂ ≠ s₁ := by
    intro heq
    subst s₂
    simp at hnodup
  have h2t1 : s₂ ≠ t₁ := by
    intro heq
    subst s₂
    simp at hnodup
  have h3s1 : t₂ ≠ s₁ := by
    intro heq
    subst t₂
    simp at hnodup
  have h3t1 : t₂ ≠ t₁ := by
    intro heq
    subst t₂
    simp at hnodup
  have h22 : s₂ ≠ t₂ := by
    intro heq
    subst s₂
    simp at hnodup
  let s : Finset V := {s₁, t₁}
  have hcard : s.card < 4 := by
    have hc : s.card = 2 := by
      dsimp [s]
      exact Finset.card_pair h11
    omega
  have hs2 : s₂ ∉ s := by
    simp only [s, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h21, h2t1⟩
  have ht2 : t₂ ∉ s := by
    simp only [s, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h3s1, h3t1⟩
  obtain ⟨p₂, hp₂path, hp₂avoid⟩ := hstrong.2 s hcard s₂ t₂ hs2 ht2 h22
  have path_of_adj : ∀ {u v : V}, D.Adj u v → digraph_is_directed_path D [u, v] u v := by
    intro u v huv
    have hne : u ≠ v := by
      rintro rfl
      exact hmulti.1 u huv
    unfold digraph_is_directed_path
    simp [huv, hne]
  have hs1mem : s₁ ∈ s := by simp [s]
  have ht1mem : t₁ ∈ s := by simp [s]
  rcases hadj with hst | hts
  · refine ⟨[s₁, t₁], p₂, Or.inl (path_of_adj hst), Or.inl hp₂path, ?_⟩
    intro a ha hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with h | h
    · rw [h] at hb
      exact (hp₂avoid s₁ hb) hs1mem
    · rw [h] at hb
      exact (hp₂avoid t₁ hb) ht1mem
  · refine ⟨[t₁, s₁], p₂, Or.inr (path_of_adj hts), Or.inl hp₂path, ?_⟩
    intro a ha hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with h | h
    · rw [h] at hb
      exact (hp₂avoid t₁ hb) ht1mem
    · rw [h] at hb
      exact (hp₂avoid s₁ hb) hs1mem
