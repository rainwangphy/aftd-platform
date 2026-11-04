import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTriangleFreeIndependentNeighborhoodCover

/-!
# simple_graph_triangle_free_independent_neighborhood_matching

Topic: combinatorics   Node: 728d861eb16b

Provenance: helper lemma. Neighborhood gluing for OP-926, https://arxiv.org/abs/2401.00392; the matching form follows from the independent-set covering condition.

In a finite triangle-free graph with no independent set of size k, if v has degree k − 1 and s is an independent set consisting of non-neighbors of v, then the vertices of s can be matched injectively to distinct neighbors of v that they are adjacent to.
-/

theorem simple_graph_triangle_free_independent_neighborhood_matching {α : Type*} [Fintype α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (k : ℕ) (htri : G.CliqueFree 3) (hfree : Gᶜ.CliqueFree k)
    (v : α) (hdegree : G.degree v + 1 = k) (s : Finset α)
    (hs : G.IsIndepSet s) (hns : ∀ x ∈ s, ¬ G.Adj v x) :
    ∃ f : {x // x ∈ s} → α, Function.Injective f ∧
      ∀ x, G.Adj v (f x) ∧ G.Adj (f x) x := by
  classical
  let L : {x // x ∈ s} → Finset α := fun x =>
    (G.neighborFinset v).filter (fun w => G.Adj w x)
  have hall : ∀ u : Finset {x // x ∈ s}, u.card ≤ (u.biUnion L).card := by
    intro u
    let J : Finset α := u.image Subtype.val
    let t : Finset α := (G.neighborFinset v).filter (fun w => ∀ x ∈ J, ¬ G.Adj w x)
    have hJ : J.card = u.card := Finset.card_image_of_injective u Subtype.val_injective
    have hJsub : (J : Set α) ⊆ s := by
      intro x hx
      simp only [J, Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact y.property
    have hbound := simple_graph_triangle_free_independent_neighborhood_cover G k htri hfree v J t
      (hs.mono hJsub) (fun x hx => hns x (hJsub hx)) (by
        intro w
        simp [t])
    have hpartition : t ∪ u.biUnion L = G.neighborFinset v := by
      ext w
      simp only [t, Finset.mem_union, Finset.mem_filter, SimpleGraph.mem_neighborFinset,
        Finset.mem_biUnion, L, J, Finset.mem_image]
      constructor
      · rintro (⟨hw, _⟩ | ⟨x, hx, hw, _⟩) <;> exact hw
      · intro hw
        by_cases he : ∃ x ∈ u, G.Adj w x
        · right
          obtain ⟨x, hx, ha⟩ := he
          exact ⟨x, hx, hw, ha⟩
        · left
          refine ⟨hw, ?_⟩
          intro x hx
          obtain ⟨y, hy, rfl⟩ := hx
          intro ha
          exact he ⟨y, hy, ha⟩
    have hdisj : Disjoint t (u.biUnion L) := by
      apply Finset.disjoint_left.mpr
      intro w hwt hwL
      obtain ⟨_, hwa⟩ := Finset.mem_filter.mp hwt
      obtain ⟨x, hx, hxl⟩ := Finset.mem_biUnion.mp hwL
      have hxJ : (x : α) ∈ J := Finset.mem_image.mpr ⟨x, hx, rfl⟩
      exact hwa x hxJ ((Finset.mem_filter.mp hxl).2)
    have hc := congrArg Finset.card hpartition
    rw [Finset.card_union_of_disjoint hdisj] at hc
    change t.card + (u.biUnion L).card = G.degree v at hc
    rw [hJ] at hbound
    omega
  obtain ⟨f, hfinj, hfmem⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' L).mp hall
  refine ⟨f, hfinj, ?_⟩
  intro x
  simpa [L] using hfmem x
