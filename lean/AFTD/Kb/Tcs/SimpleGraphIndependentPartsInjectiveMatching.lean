import AFTD.Prelude

/-!
# simple_graph_independent_parts_injective_matching

Topic: combinatorics   Node: d3ce8318d026

Provenance: helper lemma. General matching consequence for independent sets, motivated by the five-cycle link constraints for OP-926.

In a finite graph with no independent k-set, let A, B and P be disjoint independent sets, where |A|=|B|, |A|+|P|+1=k, and P has no edges to A or B. Then A can be matched injectively into B along graph edges.
-/

theorem simple_graph_independent_parts_injective_matching {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (k : ℕ) (hfree : Gᶜ.CliqueFree k)
    (A B P : Finset α) (hA : G.IsIndepSet A) (hB : G.IsIndepSet B)
    (hP : G.IsIndepSet P) (hab : Disjoint A B) (habp : Disjoint (A ∪ B) P)
    (hpa : ∀ p ∈ P, ∀ x ∈ A ∪ B, ¬ G.Adj p x)
    (hcard : A.card = B.card) (hk : A.card + P.card + 1 = k) :
    ∃ f : {x // x ∈ A} → α, Function.Injective f ∧
      ∀ x, f x ∈ B ∧ G.Adj x (f x) := by
  classical
  let L : {x // x ∈ A} → Finset α := fun x => B.filter (G.Adj x)
  have hall : ∀ u : Finset {x // x ∈ A}, u.card ≤ (u.biUnion L).card := by
    intro u
    let J : Finset α := u.image Subtype.val
    let t : Finset α := B.filter (fun y => ∀ x ∈ J, ¬ G.Adj x y)
    have hJ : J.card = u.card := Finset.card_image_of_injective u Subtype.val_injective
    have hJsub : J ⊆ A := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      exact y.property
    have hjt : Disjoint J t := by
      apply Finset.disjoint_left.mpr
      intro x hx hy
      exact (Finset.disjoint_left.mp hab) (hJsub hx) ((Finset.mem_filter.mp hy).1)
    have hjtp : Disjoint (J ∪ t) P := by
      apply Finset.disjoint_left.mpr
      intro x hx hp
      apply (Finset.disjoint_left.mp habp) _ hp
      rcases Finset.mem_union.mp hx with hx | hx
      · exact Finset.mem_union_left B (hJsub hx)
      · exact Finset.mem_union_right A ((Finset.mem_filter.mp hx).1)
    have hind : G.IsIndepSet ((J ∪ t) ∪ P : Finset α) := by
      intro x hx y hy hxy
      simp only [Finset.coe_union, Set.mem_union] at hx hy
      rcases hx with (hx | hx) | hx <;> rcases hy with (hy | hy) | hy
      · exact hA (hJsub hx) (hJsub hy) hxy
      · exact fun he => ((Finset.mem_filter.mp hy).2 x hx) he
      · exact fun he => (hpa y hy x (Finset.mem_union_left B (hJsub hx))) he.symm
      · exact fun he => ((Finset.mem_filter.mp hx).2 y hy) he.symm
      · exact hB ((Finset.mem_filter.mp hx).1) ((Finset.mem_filter.mp hy).1) hxy
      · exact fun he => (hpa y hy x (Finset.mem_union_right A ((Finset.mem_filter.mp hx).1))) he.symm
      · exact fun he => (hpa x hx y (Finset.mem_union_left B (hJsub hy))) he
      · exact fun he => (hpa x hx y (Finset.mem_union_right A ((Finset.mem_filter.mp hy).1))) he
      · exact hP hx hy hxy
    have hbound : J.card + t.card + P.card < k := by
      by_contra hn
      have hle : k ≤ ((J ∪ t) ∪ P).card := by
        rw [Finset.card_union_of_disjoint hjtp, Finset.card_union_of_disjoint hjt]
        omega
      obtain ⟨v, hv, hvc⟩ := Finset.exists_subset_card_eq hle
      apply hfree v
      apply (Gᶜ.isNClique_iff).2
      constructor
      · rw [SimpleGraph.isClique_compl]
        exact hind.mono (by exact_mod_cast hv)
      · exact hvc
    have hpartition : t ∪ u.biUnion L = B := by
      ext y
      simp only [t, Finset.mem_union, Finset.mem_filter, Finset.mem_biUnion, L, J,
        Finset.mem_image]
      constructor
      · rintro (⟨hy, _⟩ | ⟨x, hx, hy, _⟩) <;> exact hy
      · intro hy
        by_cases he : ∃ x ∈ u, G.Adj x y
        · right
          obtain ⟨x, hx, ha⟩ := he
          exact ⟨x, hx, hy, ha⟩
        · left
          refine ⟨hy, ?_⟩
          intro x hx
          obtain ⟨z, hz, rfl⟩ := hx
          intro ha
          exact he ⟨z, hz, ha⟩
    have hdisj : Disjoint t (u.biUnion L) := by
      apply Finset.disjoint_left.mpr
      intro y hyt hyL
      obtain ⟨_, hya⟩ := Finset.mem_filter.mp hyt
      obtain ⟨x, hx, hxl⟩ := Finset.mem_biUnion.mp hyL
      have hxJ : (x : α) ∈ J := Finset.mem_image.mpr ⟨x, hx, rfl⟩
      exact hya x hxJ ((Finset.mem_filter.mp hxl).2)
    have hc := congrArg Finset.card hpartition
    rw [Finset.card_union_of_disjoint hdisj] at hc
    rw [hJ] at hbound
    omega
  obtain ⟨f, hfinj, hfmem⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' L).mp hall
  refine ⟨f, hfinj, ?_⟩
  intro x
  simpa [L] using hfmem x
