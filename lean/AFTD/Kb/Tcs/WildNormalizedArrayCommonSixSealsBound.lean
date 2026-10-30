import AFTD.Prelude
import AFTD.Kb.Tcs.WildTwoMatchingsSixClosedFamilyBound

/-!
# wild_normalized_array_common_six_seals_bound

Topic: graphs   Node: 820015829a82

Provenance: helper lemma. IN-374 / OP-306, dependence estimates for the weighted partition route to https://arxiv.org/html/2610.22142v1. Elementary matching support consequence of the standard even-cycle decomposition of two disjoint perfect matchings; matching background https://dspacemainprd01.lib.uwaterloo.ca/server/api/core/bitstreams/9d33772f-c7dc-409f-a4ed-521da8d87890/content . Exact experiment9362 audits six saved15 arrays and cyclic9,13,21,27,39,61. No new wild-number bound, sharpness case or research advance is claimed.

For a symmetric idempotent row-injective array A on Fin n and two distinct colors a,b, let F consist of six-element sets S excluding a,b and closed under every a-edge and b-edge. Then 6*card(F)<=n-3. The matching partner involutions are obtained by inverting rows. Every common support excludes a,b and the b-partner of a, three distinct vertices. This bounds common six-vertex supports, not all bad cuts or their joint probabilities under a partition profile.
-/

open Finset

theorem wild_normalized_array_common_six_seals_bound
    (n : ℕ) (A : Fin n → Fin n → Fin n)
    (hdiag : ∀ x, A x x = x) (hsymm : ∀ x y, A x y = A y x)
    (hinj : ∀ x, Function.Injective (A x))
    (a b : Fin n) (hab : a ≠ b) :
    6 * (((Finset.univ : Finset (Fin n)).powersetCard 6).filter fun S =>
      a ∉ S ∧ b ∉ S ∧
      ∀ x ∈ S, ∀ y, A x y = a ∨ A x y = b → y ∈ S).card ≤ n - 3 := by
  classical
  have hbij : ∀ x, Function.Bijective (A x) := fun x =>
    ⟨hinj x, Finite.surjective_of_injective (hinj x)⟩
  let e : Fin n → Equiv.Perm (Fin n) := fun x => Equiv.ofBijective (A x) (hbij x)
  let f : Fin n → Fin n → Fin n := fun i x => (e x).symm i
  have heq : ∀ i x, A x (f i x) = i := by
    intro i x
    exact (e x).apply_symm_apply i
  have hf : ∀ i, Function.Involutive (f i) := by
    intro i x
    apply hinj (f i x)
    rw [heq, hsymm, heq]
  have hfix : ∀ i, f i i = i := by
    intro i
    apply hinj i
    rw [heq, hdiag]
  have hne : ∀ i x, i ≠ x → f i x ≠ x := by
    intro i x hix hx
    have hh := heq i x
    rw [hx, hdiag] at hh
    exact hix hh.symm
  have hpartner_a : f b a ≠ a := hne b a hab.symm
  have hpartner_b : f b a ≠ b := by
    intro h
    have hh : f b a = f b b := by rw [h, hfix]
    exact hab ((hf b).injective hh)
  let F : Finset (Finset (Fin n)) :=
    ((univ : Finset (Fin n)).powersetCard 6).filter fun S =>
      a ∉ S ∧ b ∉ S ∧
      ∀ x ∈ S, ∀ y, A x y = a ∨ A x y = b → y ∈ S
  let U : Finset (Fin n) := univ \ {a, b, f b a}
  have hF : ∀ S ∈ F, S.card = 6 ∧ a ∉ S ∧ b ∉ S ∧
      ∀ x ∈ S, ∀ y, A x y = a ∨ A x y = b → y ∈ S := by
    intro S hS
    obtain ⟨hcard, hprop⟩ := mem_filter.mp hS
    exact ⟨(mem_powersetCard.mp hcard).2, hprop⟩
  have hc : ∀ S ∈ F, ∀ x ∈ S, f a x ∈ S ∧ f b x ∈ S := by
    intro S hS x hx
    exact ⟨(hF S hS).2.2.2 x hx _ (Or.inl (heq a x)),
      (hF S hS).2.2.2 x hx _ (Or.inr (heq b x))⟩
  have hsub : ∀ S ∈ F, S ⊆ U := by
    intro S hS x hx
    apply mem_sdiff.mpr
    refine ⟨mem_univ _, ?_⟩
    intro hm
    simp only [mem_insert, mem_singleton] at hm
    rcases hm with rfl | rfl | rfl
    · exact (hF S hS).2.1 hx
    · exact (hF S hS).2.2.1 hx
    · have hh := (hc S hS (f b a) hx).2
      rw [hf b a] at hh
      exact (hF S hS).2.1 hh
  have hn : ∀ S ∈ F, ∀ x ∈ S,
      f a x ≠ x ∧ f b x ≠ x ∧ f a x ≠ f b x := by
    intro S hS x hx
    refine ⟨hne a x (by intro h; subst x; exact (hF S hS).2.1 hx),
      hne b x (by intro h; subst x; exact (hF S hS).2.2.1 hx), ?_⟩
    intro h
    have hh := congrArg (A x) h
    rw [heq, heq] at hh
    exact hab hh
  have hbound := wild_two_matchings_six_closed_family_bound (f a) (f b)
    (hf a) (hf b) F U (fun S hS => (hF S hS).1) hsub hc hn
  have hthree : ({a, b, f b a} : Finset (Fin n)).card = 3 := by
    simp [hab, hpartner_a, hpartner_b, Ne.symm hpartner_a, Ne.symm hpartner_b]
  have hU : U.card = n - 3 := by
    dsimp [U]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp [hthree]
  rw [hU] at hbound
  exact hbound
