import AFTD.Prelude
import AFTD.Kb.Tcs.IsRankedPoset
import AFTD.Kb.Tcs.WeakSl2Action

/-!
# weak_sl2_hall_condition

Topic: combinatorics   Node: 6dd904039e72

Provenance: helper lemma. arXiv:2610.24148 Theorem 4.1 "Strong sl_2 Actions and Symmetric Chain Decompositions"

Let α be a finite partially ordered type with decidable equality and an integer rank function rank : α → ℤ. If rank makes α a ranked poset and E, F, H : Module.End ℂ (α → ℂ) define a weak sl_2-action, and for an integer n the raising operator E is injective on functions supported on rank n, then for every subset A of the level set of rank n, the cardinality of A is at most the cardinality of the set of elements in the level set of rank n + 2 that cover some element of A.
-/

open scoped Classical in
/-- The marriage condition holds between adjacent levels when the raising operator is injective and supported on covers. -/
theorem weak_sl2_hall_condition
    {α : Type*} [Fintype α] [DecidableEq α] [PartialOrder α]
    (rank : α → ℤ)
    (hrk : is_ranked_poset rank)
    (E F H : Module.End ℂ (α → ℂ))
    (hact : weak_sl2_action rank E F H)
    (n : ℤ)
    (hinj : ∀ (v : α → ℂ), (∀ x, v x ≠ 0 → rank x = n) → E v = 0 → v = 0)
    (A : Finset {x : α // rank x = n}) :
    A.card ≤ (Finset.univ.filter (fun y : {y : α // rank y = n + 2} => ∃ a ∈ A, (a : α) ⋖ (y : α))).card := by
  classical
  set N : Finset {y : α // rank y = n + 2} :=
    Finset.univ.filter (fun y => ∃ a ∈ A, (a : α) ⋖ (y : α)) with hN
  have hsupp : ∀ (a : A) (y : α), E (Pi.single (a:α) (1:ℂ)) y ≠ 0 →
      ∃ b : N, (((b : N) : {y : α // rank y = n + 2}) : α) = y := by
    intro a y hy
    have hra : rank (a:α) = n := (a : {x : α // rank x = n}).2
    have hcover : (a:α) ⋖ y := hact.2.2.2.2 (a:α) y hy
    have hrank : rank y = n + 2 := by
      have h := hrk.2.1 hcover
      rw [hra] at h
      exact h
    refine ⟨⟨⟨y, hrank⟩, ?_⟩, rfl⟩
    rw [hN]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (a : {x : α // rank x = n}), a.2, hcover⟩
  let L : (A → ℂ) →ₗ[ℂ] (α → ℂ) :=
    { toFun := fun c => ∑ a : A, c a • (Pi.single (a:α) (1:ℂ) : α → ℂ)
      map_add' := by
        intro c d
        simp [Finset.sum_add_distrib, add_smul]
      map_smul' := by
        intro r c
        simp [Finset.smul_sum, smul_smul] }
  let φ : (A → ℂ) →ₗ[ℂ] (N → ℂ) :=
    { toFun := fun c y => E (L c) (((y : N) : {y : α // rank y = n + 2}) : α)
      map_add' := by
        intro c d
        ext y
        simp
      map_smul' := by
        intro r c
        ext y
        simp }
  have key : ∀ c : A → ℂ, φ c = 0 → c = 0 := by
    intro c hc
    have hv_supp : ∀ x, L c x ≠ 0 → rank x = n := by
      intro x hx
      by_contra hcon
      apply hx
      change (∑ a : A, c a • (Pi.single (a:α) (1:ℂ) : α → ℂ)) x = 0
      rw [Finset.sum_apply]
      apply Finset.sum_eq_zero
      intro a _
      have hane : (a:α) ≠ x := by
        rintro rfl
        exact hcon (a : {x : α // rank x = n}).2
      simp [Pi.single_eq_of_ne (Ne.symm hane)]
    have hEsupp : ∀ x : α, E (L c) x ≠ 0 →
        ∃ b : N, (((b : N) : {y : α // rank y = n + 2}) : α) = x := by
      intro x hx
      by_contra hcon
      apply hx
      change E (∑ a : A, c a • (Pi.single (a:α) (1:ℂ) : α → ℂ)) x = 0
      rw [map_sum]
      rw [Finset.sum_apply]
      apply Finset.sum_eq_zero
      intro a _
      rw [map_smul]
      have hzero : E (Pi.single (a:α) (1:ℂ)) x = 0 := by
        by_contra hne
        exact hcon (hsupp a x hne)
      simp [hzero]
    have hEv0 : E (L c) = 0 := by
      funext x
      by_contra hx
      obtain ⟨b, hb⟩ := hEsupp x hx
      have hN0 : E (L c) (((b : N) : {y : α // rank y = n + 2}) : α) = 0 := by
        have := congrFun hc b
        simpa [φ] using this
      exact hx (hb ▸ hN0)
    have hLc0 : L c = 0 := hinj (L c) hv_supp hEv0
    funext a
    have hval : L c (a:α) = c a := by
      change (∑ b : A, c b • (Pi.single (b:α) (1:ℂ) : α → ℂ)) (a:α) = c a
      rw [Finset.sum_apply]
      rw [Finset.sum_eq_single a]
      · simp
      · intro b _ hb
        have hne : (b:α) ≠ (a:α) := by
          rintro h
          exact hb (Subtype.ext (Subtype.ext h))
        simp [Pi.single_eq_of_ne (Ne.symm hne)]
      · intro h
        exact absurd (Finset.mem_univ a) h
    rw [← hval, hLc0]
    simp
  have hinjφ : Function.Injective φ := by
    intro c d hcd
    have h1 : φ (c - d) = 0 := by
      rw [map_sub, hcd, sub_self]
    have h2 : c - d = 0 := key (c - d) h1
    exact sub_eq_zero.mp h2
  have hfin := LinearMap.finrank_le_finrank_of_injective hinjφ
  rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card] at hfin
  rwa [Fintype.card_coe, Fintype.card_coe] at hfin
