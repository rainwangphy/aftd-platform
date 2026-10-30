import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphIsTournament
import AFTD.Kb.Tcs.DigraphIsKStrong
import AFTD.Kb.Tcs.DigraphIsUnilaterallyTwoLinked
import AFTD.Kb.Tcs.DigraphIsDirectedPath

/-!
# digraph_four_strong_tournament_unilaterally_two_linked

Topic: graphs   Node: 1ea0939ff1fa

Provenance: original. Related work: arXiv:2610.36895 Sec. 1 and Sec. 5

Let D be a digraph on a finite type V. If D is a tournament and D is 4-strong, then D is unilaterally 2-linked.
-/

private lemma digraph_four_strong_tournament_unilaterally_two_linked_lists_disjoint {V : Type*} {a b c d : V}
    (h : [a,b,c,d].Nodup) :
    List.Disjoint [a,b] [c,d] ∧ List.Disjoint [a,b] [d,c] ∧
    List.Disjoint [b,a] [c,d] ∧ List.Disjoint [b,a] [d,c] := by
  simp at h
  obtain ⟨⟨hab, hac, had⟩, ⟨hbc, hbd⟩, hcd⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [List.Disjoint, List.mem_cons, List.not_mem_nil, or_false]
    rintro x (hxa | hxb) (hyc | hyd)
    · exact hac (hxa.symm.trans hyc)
    · exact had (hxa.symm.trans hyd)
    · exact hbc (hxb.symm.trans hyc)
    · exact hbd (hxb.symm.trans hyd)
  · simp only [List.Disjoint, List.mem_cons, List.not_mem_nil, or_false]
    rintro x (hxa | hxb) (hyd | hyc)
    · exact had (hxa.symm.trans hyd)
    · exact hac (hxa.symm.trans hyc)
    · exact hbd (hxb.symm.trans hyd)
    · exact hbc (hxb.symm.trans hyc)
  · simp only [List.Disjoint, List.mem_cons, List.not_mem_nil, or_false]
    rintro x (hxb | hxa) (hyc | hyd)
    · exact hbc (hxb.symm.trans hyc)
    · exact hbd (hxb.symm.trans hyd)
    · exact hac (hxa.symm.trans hyc)
    · exact had (hxa.symm.trans hyd)
  · simp only [List.Disjoint, List.mem_cons, List.not_mem_nil, or_false]
    rintro x (hxb | hxa) (hyd | hyc)
    · exact hbd (hxb.symm.trans hyd)
    · exact hbc (hxb.symm.trans hyc)
    · exact had (hxa.symm.trans hyd)
    · exact hac (hxa.symm.trans hyc)

private lemma digraph_four_strong_tournament_unilaterally_two_linked_path_of_adj
    {V : Type*} (D : Digraph V) (hirr : ∀ x, ¬ D.Adj x x) {x y : V} (hxy : D.Adj x y) :
    digraph_is_directed_path D [x, y] x y := by
  have hne : x ≠ y := by rintro rfl; exact hirr x hxy
  exact ⟨by simp [hxy], by simp [hne], rfl, rfl⟩

/-- Every 4-strong tournament is unilaterally 2-linked. -/
theorem digraph_four_strong_tournament_unilaterally_two_linked
    {V : Type*} [Fintype V] (D : Digraph V)
    (htourn : digraph_is_tournament D)
    (hstrong : digraph_is_k_strong D 4) :
    digraph_is_unilaterally_two_linked D := by
  obtain ⟨hirr, hanti⟩ := htourn
  intro s₁ t₁ s₂ t₂ hnd
  obtain ⟨hd11, hd12, hd21, hd22⟩ :=
    digraph_four_strong_tournament_unilaterally_two_linked_lists_disjoint hnd
  simp at hnd
  have hne1 : s₁ ≠ t₁ := hnd.1.1
  have hne2 : s₂ ≠ t₂ := hnd.2.2
  have h1 : D.Adj s₁ t₁ ∨ D.Adj t₁ s₁ := by
    by_cases hh : D.Adj s₁ t₁
    · exact Or.inl hh
    · exact Or.inr (by_contra fun hc => hh ((hanti s₁ t₁ hne1).mpr hc))
  have h2 : D.Adj s₂ t₂ ∨ D.Adj t₂ s₂ := by
    by_cases hh : D.Adj s₂ t₂
    · exact Or.inl hh
    · exact Or.inr (by_contra fun hc => hh ((hanti s₂ t₂ hne2).mpr hc))
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact ⟨[s₁,t₁], [s₂,t₂], Or.inl (digraph_four_strong_tournament_unilaterally_two_linked_path_of_adj D hirr h1),
      Or.inl (digraph_four_strong_tournament_unilaterally_two_linked_path_of_adj D hirr h2), hd11⟩
  · exact ⟨[s₁,t₁], [t₂,s₂], Or.inl (digraph_four_strong_tournament_unilaterally_two_linked_path_of_adj D hirr h1),
      Or.inr (digraph_four_strong_tournament_unilaterally_two_linked_path_of_adj D hirr h2), hd12⟩
  · exact ⟨[t₁,s₁], [s₂,t₂], Or.inr (digraph_four_strong_tournament_unilaterally_two_linked_path_of_adj D hirr h1),
      Or.inl (digraph_four_strong_tournament_unilaterally_two_linked_path_of_adj D hirr h2), hd21⟩
  · exact ⟨[t₁,s₁], [t₂,s₂], Or.inr (digraph_four_strong_tournament_unilaterally_two_linked_path_of_adj D hirr h1),
      Or.inr (digraph_four_strong_tournament_unilaterally_two_linked_path_of_adj D hirr h2), hd22⟩
