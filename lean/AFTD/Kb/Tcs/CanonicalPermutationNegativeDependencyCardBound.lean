import AFTD.Prelude
import AFTD.Kb.Tcs.PermutationPartialAssignmentCardBoundOfSwitching

/-!
# canonical_permutation_negative_dependency_card_bound

Topic: graphs   Node: 00f017f88c66

Provenance: helper lemma. Negative-dependency counting helper for OP-306; EJC 14 (2007) R63, DOI 10.37236/981, Theorem 1, specialized to the domain/range-overlap supergraph.

For canonical permutation events with disjoint domains and ranges from a fixed injective partial assignment, multiplying the avoiding permutations that extend it by the relevant falling factorial bounds them by all avoiding permutations.
-/

theorem canonical_permutation_negative_dependency_card_bound
    {α I : Type*} [Fintype α] [DecidableEq α]
    (D : Finset α) (f : α → α) (hf : Set.InjOn f (↑D : Set α))
    (T : Finset I) (C : I → Finset α) (g : I → α → α)
    (hdom : ∀ i ∈ T, Disjoint D (C i))
    (hran : ∀ i ∈ T, Disjoint (D.image f) ((C i).image (g i))) :
    (Fintype.card α).descFactorial D.card *
      ((Finset.univ.filter (fun τ : Equiv.Perm α =>
        ∀ i ∈ T, ∃ v ∈ C i, τ v ≠ g i v)).filter
          (fun τ => ∀ a ∈ D, τ a = f a)).card ≤
      (Finset.univ.filter (fun τ : Equiv.Perm α =>
        ∀ i ∈ T, ∃ v ∈ C i, τ v ≠ g i v)).card := by
  classical
  apply permutation_partial_assignment_card_bound_of_switching D f hf
  intro a ha τ hτ hτa y
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro i hi
  by_contra h
  push Not at h
  obtain ⟨v, hv, hτv⟩ := (Finset.mem_filter.mp hτ).2 i hi
  have hva : v ≠ a := by
    intro heq
    exact Finset.disjoint_left.mp (hdom i hi) ha (heq ▸ hv)
  have hgfa : g i v ≠ f a := by
    intro heq
    exact Finset.disjoint_left.mp (hran i hi)
      (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
      (Finset.mem_image.mpr ⟨v, hv, heq⟩)
  have hsva : (Equiv.swap y (f a) * τ) a = y := by
    simp [Equiv.Perm.mul_apply, hτa]
  have hgy : g i v ≠ y := by
    intro heq
    apply hva
    exact (Equiv.swap y (f a) * τ).injective ((h v hv).trans (heq.trans hsva.symm))
  apply hτv
  have hh := congrArg (Equiv.swap y (f a)) (h v hv)
  simpa only [Equiv.Perm.mul_apply, Equiv.swap_apply_self,
    Equiv.swap_apply_of_ne_of_ne hgy hgfa] using hh
