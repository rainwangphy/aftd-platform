import AFTD.Prelude

/-!
# wild_two_matchings_small_closed_sets_disjoint_or_equal

Topic: graphs   Node: cfd536c4c009

Provenance: helper lemma. IN-374 / OP-306, dependence estimates for the weighted partition route to https://arxiv.org/html/2610.22142v1. Elementary matching support consequence of the standard even-cycle decomposition of two disjoint perfect matchings; matching background https://dspacemainprd01.lib.uwaterloo.ca/server/api/core/bitstreams/9d33772f-c7dc-409f-a4ed-521da8d87890/content . Exact experiment9362 audits six saved15 arrays and cyclic9,13,21,27,39,61. No new wild-number bound, sharpness case or research advance is claimed.

For two involutions on a decidable type, finite sets S,T of cardinality at most7 that are closed under both maps are disjoint or equal, provided both maps have no fixed points on S union T and have distinct values at each point there. Each nonempty closed set has at least4 points, so intersection and difference cannot both be nonempty.
-/

open Finset

theorem wild_two_involutions_closed_card_ge_four
    {α : Type*} [DecidableEq α] (f g : α → α)
    (hf : Function.Involutive f) (S : Finset α)
    (hc : ∀ x ∈ S, f x ∈ S ∧ g x ∈ S)
    (hn : ∀ x ∈ S, f x ≠ x ∧ g x ≠ x ∧ f x ≠ g x)
    (hne : S.Nonempty) : 4 ≤ S.card := by
  obtain ⟨x, hx⟩ := hne
  have hfx := (hc x hx).1
  have hgx := (hc x hx).2
  have hfgx := (hc (g x) hgx).1
  obtain ⟨h1, h2, h3⟩ := hn x hx
  have h4 : f (g x) ≠ x := by
    intro h
    have h' := congrArg f h
    rw [hf (g x)] at h'
    exact h3 h'.symm
  have h5 : f (g x) ≠ f x := by
    intro h
    exact h2 (hf.injective h)
  have h6 : f (g x) ≠ g x := (hn (g x) hgx).1
  have hcard : ({x, f x, g x, f (g x)} : Finset α).card = 4 := by
    simp [h1, h2, h3, h4, h5, h6, Ne.symm h1, Ne.symm h2,
      Ne.symm h3, Ne.symm h4, Ne.symm h5, Ne.symm h6]
  rw [← hcard]
  apply Finset.card_le_card
  intro y hy
  simp only [mem_insert, mem_singleton] at hy
  rcases hy with rfl | rfl | rfl | rfl <;> assumption

theorem wild_two_involutions_small_closed_subset
    {α : Type*} [DecidableEq α] (f g : α → α)
    (hf : Function.Involutive f) (hg : Function.Involutive g)
    (S T : Finset α) (hsize : S.card ≤ 7)
    (hS : ∀ x ∈ S, f x ∈ S ∧ g x ∈ S)
    (hT : ∀ x ∈ T, f x ∈ T ∧ g x ∈ T)
    (hn : ∀ x ∈ S, f x ≠ x ∧ g x ≠ x ∧ f x ≠ g x)
    (hi : (S ∩ T).Nonempty) : S ⊆ T := by
  have hi4 : 4 ≤ (S ∩ T).card := by
    apply wild_two_involutions_closed_card_ge_four f g hf _ _ _ hi
    · intro x hx
      obtain ⟨hs, ht⟩ := mem_inter.mp hx
      exact ⟨mem_inter.mpr ⟨(hS x hs).1, (hT x ht).1⟩,
        mem_inter.mpr ⟨(hS x hs).2, (hT x ht).2⟩⟩
    · intro x hx
      exact hn x (mem_inter.mp hx).1
  by_contra hsub
  have hd : (S \ T).Nonempty := by
    obtain ⟨x, hx, hxt⟩ := Finset.not_subset.mp hsub
    exact ⟨x, mem_sdiff.mpr ⟨hx, hxt⟩⟩
  have hd4 : 4 ≤ (S \ T).card := by
    apply wild_two_involutions_closed_card_ge_four f g hf _ _ _ hd
    · intro x hx
      obtain ⟨hs, ht⟩ := mem_sdiff.mp hx
      constructor
      · apply mem_sdiff.mpr
        refine ⟨(hS x hs).1, ?_⟩
        intro h
        have h' := (hT (f x) h).1
        rw [hf x] at h'
        exact ht h'
      · apply mem_sdiff.mpr
        refine ⟨(hS x hs).2, ?_⟩
        intro h
        have h' := (hT (g x) h).2
        rw [hg x] at h'
        exact ht h'
    · intro x hx
      exact hn x (mem_sdiff.mp hx).1
  have heq := Finset.card_sdiff_add_card_inter S T
  omega

theorem wild_two_matchings_small_closed_sets_disjoint_or_equal
    {α : Type*} [DecidableEq α] (f g : α → α)
    (hf : Function.Involutive f) (hg : Function.Involutive g)
    (S T : Finset α) (hSsize : S.card ≤ 7) (hTsize : T.card ≤ 7)
    (hS : ∀ x ∈ S, f x ∈ S ∧ g x ∈ S)
    (hT : ∀ x ∈ T, f x ∈ T ∧ g x ∈ T)
    (hn : ∀ x ∈ S ∪ T, f x ≠ x ∧ g x ≠ x ∧ f x ≠ g x) :
    Disjoint S T ∨ S = T := by
  by_cases hd : Disjoint S T
  · exact Or.inl hd
  right
  have hi : (S ∩ T).Nonempty := by
    obtain ⟨x, hxS, hxT⟩ := Finset.not_disjoint_iff.mp hd
    exact ⟨x, mem_inter.mpr ⟨hxS, hxT⟩⟩
  apply Finset.Subset.antisymm
  · exact wild_two_involutions_small_closed_subset f g hf hg S T hSsize hS hT
      (fun x hx => hn x (mem_union_left T hx)) hi
  · exact wild_two_involutions_small_closed_subset f g hf hg T S hTsize hT hS
      (fun x hx => hn x (mem_union_right S hx)) (by simpa [inter_comm] using hi)
