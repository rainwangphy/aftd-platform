import AFTD.Prelude
import AFTD.Kb.Tcs.CardPiFinsetFilterApplyMem
import AFTD.Kb.Tcs.F

/-!
# schwartz_zippel_zero_count_tight

Topic: algebraic_complexity   Node: 4b3b2efbba56

Provenance: original. Related work: Burgisser, Clausen & Shokrollahi, Algebraic Complexity Theory

For any integral domain F with decidable equality, any positive integer n, any finite subset S of F, and any natural number d with d ≤ S.card, there exists a nonzero multivariate polynomial p in n variables over F with total degree at most d such that the number of points in S^n at which p evaluates to zero equals d * S.card ^ (n - 1).
-/

lemma schwartz_zippel_zero_count_tight_x_sub_c_ne_zero {F : Type*} [CommRing F] [IsDomain F]
    {n : ℕ} (i : Fin n) (s : F) : (MvPolynomial.X i - MvPolynomial.C s : MvPolynomial (Fin n) F) ≠ 0 := by
  intro h
  have h2 := congr_arg (MvPolynomial.coeff (Finsupp.single i 1)) h
  rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_zero, MvPolynomial.coeff_X, if_pos rfl, MvPolynomial.coeff_C] at h2
  have hne : (0 : Fin n →₀ ℕ) ≠ Finsupp.single i 1 := by
    intro h3
    have h4 := Finsupp.ext_iff.mp h3 i
    simp at h4
  rw [if_neg hne, sub_zero] at h2
  exact one_ne_zero h2

/-- Tightness of the Schwartz-Zippel zero count upper bound via a product of univariate linear factors. -/
theorem schwartz_zippel_zero_count_tight {F : Type*} [CommRing F] [IsDomain F] [DecidableEq F]
    {n : ℕ} (hn : 0 < n) {S : Finset F} {d : ℕ} (hd : d ≤ S.card) :
    ∃ p : MvPolynomial (Fin n) F, p ≠ 0 ∧ p.totalDegree ≤ d ∧
      Finset.card (Finset.filter (fun x => MvPolynomial.eval x p = 0)
        (Fintype.piFinset (fun _ : Fin n => S))) = d * S.card ^ (n - 1) := by
  obtain ⟨T, hT, hTcard⟩ := Finset.exists_subset_card_eq hd
  let i₀ : Fin n := ⟨0, hn⟩
  let p : MvPolynomial (Fin n) F := ∏ s ∈ T, (MvPolynomial.X i₀ - MvPolynomial.C s)
  use p
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    intro s hs
    exact schwartz_zippel_zero_count_tight_x_sub_c_ne_zero i₀ s
  · refine (MvPolynomial.totalDegree_finsetProd T _).trans ?_
    have h1 (s : F) (hs : s ∈ T) :
        (MvPolynomial.X i₀ - MvPolynomial.C s : MvPolynomial (Fin n) F).totalDegree ≤ 1 :=
      (MvPolynomial.totalDegree_sub_C_le (MvPolynomial.X i₀) s).trans (MvPolynomial.totalDegree_X i₀).le
    have h2 : ∑ s ∈ T, (MvPolynomial.X i₀ - MvPolynomial.C s : MvPolynomial (Fin n) F).totalDegree ≤ ∑ s ∈ T, 1 :=
      Finset.sum_le_sum h1
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h2
    rw [hTcard] at h2
    exact h2
  · have h_filter :
        Finset.filter (fun x => MvPolynomial.eval x p = 0) (Fintype.piFinset (fun _ : Fin n => S)) =
        Finset.filter (fun x => x i₀ ∈ T) (Fintype.piFinset (fun _ : Fin n => S)) := by
      apply Finset.filter_congr
      intro x hx
      dsimp [p]
      rw [map_prod]
      have : (∏ s ∈ T, MvPolynomial.eval x (MvPolynomial.X i₀ - MvPolynomial.C s)) = ∏ s ∈ T, (x i₀ - s) := by
        apply Finset.prod_congr rfl
        intro s hs
        simp
      rw [this, Finset.prod_eq_zero_iff]
      simp [sub_eq_zero]
    rw [h_filter]
    rw [card_piFinset_filter_apply_mem hn S T hT i₀]
    rw [hTcard]
