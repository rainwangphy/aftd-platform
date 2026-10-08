import AFTD.Prelude
import AFTD.Kb.Tcs.MatroidStronglyBaseOrderable
import AFTD.Kb.Tcs.MatroidCommonColorable
import AFTD.Kb.Tcs.MatroidCommonListColorable
import AFTD.Kb.Tcs.MatroidSboReductionPairsOfTwoIndep
import AFTD.Kb.Tcs.ListColorableTwoOfTwoInvolutions

/-!
# matroid_sbo_list_colorable_two_of_colorable_two

Topic: combinatorics   Node: 787747c61f1f

Provenance: formalization of a published result. Source: arXiv:2610.07318 (A note on the list chromatic number of two matroids), Corollary 2.3 (first statement), proved there via Proposition 2.2 (reduction to a partition matroid with classes of size at most two) and the list edge-coloring theorem for bipartite multigraphs of maximum degree two. Single-matroid 2-colorability is written as a common 2-coloring of the pair (M, M).

If M₁ and M₂ are strongly base-orderable matroids on a common finite ground set and each of them is 2-colorable (its ground set is the union of two independent sets), then the pair (M₁, M₂) is 2-list-colorable: from any lists of at least two colors per element one can choose colors so that every color class is independent in both matroids.
-/

theorem matroid_sbo_list_colorable_two_of_colorable_two {α : Type*} (M₁ M₂ : Matroid α)
    [M₁.Finite] (hE : M₁.E = M₂.E)
    (h₁ : matroid_strongly_base_orderable M₁) (h₂ : matroid_strongly_base_orderable M₂)
    (c₁ : matroid_common_colorable M₁ M₁ 2) (c₂ : matroid_common_colorable M₂ M₂ 2) :
    matroid_common_list_colorable M₁ M₂ 2 := by
  classical
  have : M₂.Finite := ⟨hE ▸ M₁.ground_finite⟩
  -- each matroid reduces to a partition matroid with classes of size at most two
  have red : ∀ (M : Matroid α) [M.Finite], matroid_strongly_base_orderable M →
      matroid_common_colorable M M 2 → ∃ p : α → α, Function.Involutive p ∧
        ∀ T ⊆ M.E, (∀ e ∈ T, p e ∈ T → p e = e) → M.Indep T := by
    intro M _ hM ⟨c, hc, hind⟩
    refine matroid_sbo_reduction_pairs_of_two_indep M hM {e | e ∈ M.E ∧ c e = 0}
      {e | e ∈ M.E ∧ c e = 1} (hind 0).1 (hind 1).1 ?_ ?_
    · rw [Set.disjoint_left]
      rintro e ⟨-, h0⟩ ⟨-, h1⟩
      omega
    · ext e
      simp only [Set.mem_union, Set.mem_ofPred_eq]
      constructor
      · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
      · intro h
        have := hc e h
        by_cases h0 : c e = 0
        · exact Or.inl ⟨h, h0⟩
        · exact Or.inr ⟨h, by omega⟩
  obtain ⟨p, hp, hpT⟩ := red M₁ h₁ c₁
  obtain ⟨q, hq, hqT⟩ := red M₂ h₂ c₂
  intro L hL
  obtain ⟨c, hcL, hc⟩ := list_colorable_two_of_two_involutions M₁.E M₁.ground_finite p q hp hq
    L hL
  refine ⟨c, hcL, fun γ => ⟨?_, ?_⟩⟩
  · refine hpT _ (fun e he => he.1) ?_
    rintro e ⟨he, hγ⟩ ⟨hpe, hpγ⟩
    by_contra hne
    exact (hc e he).1 hpe hne (hpγ.trans hγ.symm)
  · refine hqT _ (fun e he => hE ▸ he.1) ?_
    rintro e ⟨he, hγ⟩ ⟨hqe, hqγ⟩
    by_contra hne
    exact (hc e he).2 hqe hne (hqγ.trans hγ.symm)
