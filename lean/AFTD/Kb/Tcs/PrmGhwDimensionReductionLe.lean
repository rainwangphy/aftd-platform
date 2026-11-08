import AFTD.Prelude
import AFTD.Kb.Tcs.PrmGhwDimensionReductionZero
import AFTD.Kb.Tcs.PrmGHW
import AFTD.Kb.Tcs.GeneralizedHammingWeight
import AFTD.Kb.Tcs.PrmCode
import AFTD.Kb.Tcs.PrmDim
import AFTD.Kb.Tcs.PrmEvalMap
import AFTD.Kb.Tcs.Monomial
import AFTD.Kb.Tcs.Support

/-!
# prm_ghw_dimension_reduction_le

Topic: information   Node: 1b77084ef548

Provenance: formalization of a published result. Source: arXiv:2611.08203 Lemma 6.10

Let K be a finite field of order q, let e, m ≥ 1, 0 ≤ t ≤ m - 1, and h = m - t. For every 1 ≤ r ≤ k_e(h), the r-th generalized Hamming weight d_r(PRM_q(e + t(q - 1), m)) is at most d_r(PRM_q(e, m - t)).
-/

open MvPolynomial Classical in
/-- index of a variable occurring in a monomial (0 if none) -/
noncomputable def prmLiftVar {h : ℕ} (μ : Fin (h + 1) →₀ ℕ) : Fin (h + 1) :=
  if hμ : μ.support.Nonempty then hμ.choose else 0

open MvPolynomial Classical in
/-- The lift of a monomial (Lemma 6.2 applied t times). -/
noncomputable def prmLiftMono (K : Type*) [Field K] (h t q : ℕ) (μ : Fin (h + 1) →₀ ℕ) :
    MvPolynomial (Fin (h + t + 1)) K :=
  rename (fun j : Fin (h + 1) => (⟨j + t, by omega⟩ : Fin (h + t + 1))) (monomial μ 1) *
    ∏ s : Fin t, (X (⟨prmLiftVar μ + t, by omega⟩ : Fin (h + t + 1)) ^ (q - 1) -
      X (⟨s, by omega⟩ : Fin (h + t + 1)) ^ (q - 1))

open MvPolynomial Classical in
theorem prmLiftMono_eval (K : Type*) [Field K] [Fintype K] (h t : ℕ) (μ : Fin (h + 1) →₀ ℕ)
    (hμ : μ.support.Nonempty) (v : Fin (h + t + 1) → K) :
    eval v (prmLiftMono K h t (Fintype.card K) μ) =
      if (∀ s : Fin t, v ⟨s, by omega⟩ = 0) then
        eval (fun j : Fin (h + 1) => v ⟨j + t, by omega⟩) (monomial μ 1) else 0 := by
  have hq : 2 ≤ Fintype.card K := by
    have := Fintype.one_lt_card (α := K); omega
  have hiμ : prmLiftVar μ ∈ μ.support := by
    rw [prmLiftVar, dif_pos hμ]; exact hμ.choose_spec
  have hmono : eval v (rename (fun j : Fin (h + 1) => (⟨j + t, by omega⟩ : Fin (h + t + 1)))
      (monomial μ 1)) = eval (fun j : Fin (h + 1) => v ⟨j + t, by omega⟩) (monomial μ 1) := by
    rw [eval_rename]; rfl
  have hzero : v ⟨prmLiftVar μ + t, by omega⟩ = 0 →
      eval (fun j : Fin (h + 1) => v ⟨j + t, by omega⟩) (monomial μ 1) = 0 := by
    intro hv
    rw [eval_monomial, one_mul]
    apply Finset.prod_eq_zero hiμ
    simp only [hv]
    apply zero_pow
    exact (Finsupp.mem_support_iff.mp hiμ)
  unfold prmLiftMono
  rw [map_mul, hmono, map_prod]
  simp only [map_sub, map_pow, eval_X]
  by_cases hall : ∀ s : Fin t, v ⟨s, by omega⟩ = 0
  · rw [if_pos hall]
    by_cases hvi : v ⟨prmLiftVar μ + t, by omega⟩ = 0
    · rw [hzero hvi, zero_mul]
    · have h1 : v ⟨prmLiftVar μ + t, by omega⟩ ^ (Fintype.card K - 1) = 1 := FiniteField.pow_card_sub_one_eq_one _ hvi
      simp only [h1, hall]
      rw [zero_pow (by omega)]
      simp
  · rw [if_neg hall]
    push Not at hall
    obtain ⟨s, hs⟩ := hall
    by_cases hvi : v ⟨prmLiftVar μ + t, by omega⟩ = 0
    · rw [hzero hvi, zero_mul]
    · apply mul_eq_zero_of_right
      apply Finset.prod_eq_zero (Finset.mem_univ s)
      rw [FiniteField.pow_card_sub_one_eq_one _ hvi, FiniteField.pow_card_sub_one_eq_one _ hs,
        sub_self]

open MvPolynomial Classical in
/-- The linear lift of polynomials. -/
noncomputable def prmLift (K : Type*) [Field K] (h t q : ℕ) :
    MvPolynomial (Fin (h + 1)) K →ₗ[K] MvPolynomial (Fin (h + t + 1)) K :=
  (basisMonomials (Fin (h + 1)) K).constr K (prmLiftMono K h t q)

open MvPolynomial Classical in
theorem prmLift_eq_sum (K : Type*) [Field K] (h t q : ℕ) (F : MvPolynomial (Fin (h + 1)) K) :
    prmLift K h t q F = ∑ μ ∈ F.support, coeff μ F • prmLiftMono K h t q μ := by
  conv_lhs => rw [F.as_sum]
  rw [map_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have : monomial μ (coeff μ F) = coeff μ F • (basisMonomials (Fin (h + 1)) K) μ := by
    rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [this, map_smul, prmLift, Module.Basis.constr_basis]

open MvPolynomial Classical in
theorem prmLift_eval (K : Type*) [Field K] [Fintype K] (h t e : ℕ) (he : 1 ≤ e)
    (F : MvPolynomial (Fin (h + 1)) K) (hF : F.IsHomogeneous e) (v : Fin (h + t + 1) → K) :
    eval v (prmLift K h t (Fintype.card K) F) =
      if (∀ s : Fin t, v ⟨s, by omega⟩ = 0) then
        eval (fun j : Fin (h + 1) => v ⟨j + t, by omega⟩) F else 0 := by
  rw [prmLift_eq_sum, map_sum]
  simp only [smul_eval]
  have hne : ∀ μ ∈ F.support, μ.support.Nonempty := by
    intro μ hμ
    rw [Finsupp.support_nonempty_iff]
    rintro rfl
    have := hF (mem_support_iff.mp hμ)
    simp at this; omega
  rw [Finset.sum_congr rfl fun μ hμ => by rw [prmLiftMono_eval K h t μ (hne μ hμ) v]]
  split_ifs with hall
  · conv_rhs => rw [F.as_sum]
    rw [map_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [eval_monomial, eval_monomial, one_mul]
  · simp

open MvPolynomial Classical in
theorem prmLift_isHomogeneous (K : Type*) [Field K] (h t q e : ℕ) (he : 1 ≤ e)
    (F : MvPolynomial (Fin (h + 1)) K) (hF : F.IsHomogeneous e) :
    (prmLift K h t q F).IsHomogeneous (e + t * (q - 1)) := by
  rw [prmLift_eq_sum]
  apply IsHomogeneous.sum
  intro μ hμ
  rw [smul_eq_C_mul]
  apply IsHomogeneous.C_mul
  unfold prmLiftMono
  apply IsHomogeneous.mul
  · apply IsHomogeneous.rename_isHomogeneous
    apply isHomogeneous_monomial
    rw [Finsupp.degree_eq_weight_one]
    exact hF (mem_support_iff.mp hμ)
  · have := IsHomogeneous.prod (Finset.univ : Finset (Fin t))
      (fun s : Fin t => (X (⟨prmLiftVar μ + t, by omega⟩ : Fin (h + t + 1)) ^ (q - 1) -
        X (⟨s, by omega⟩ : Fin (h + t + 1)) ^ (q - 1) : MvPolynomial (Fin (h + t + 1)) K))
      (fun _ => q - 1) (fun s _ => (isHomogeneous_X_pow _ _).sub (isHomogeneous_X_pow _ _))
    simpa using this

open MvPolynomial Classical in
theorem prm_isHomogeneous_eval_smul {σ K : Type*} [Field K] [Fintype σ] {n : ℕ}
    (F : MvPolynomial σ K) (hF : F.IsHomogeneous n) (c : K) (v : σ → K) :
    eval (c • v) F = c ^ n * eval v F := by
  conv_lhs => rw [F.as_sum]
  conv_rhs => rw [F.as_sum]
  simp only [map_sum, eval_monomial, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have hdeg : μ.degree = n := by
    rw [Finsupp.degree_eq_weight_one]; exact hF (mem_support_iff.mp hμ)
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [Finsupp.prod_mul]
  have : (μ.prod fun _ e => c ^ e) = c ^ n := by
    rw [← hdeg, Finsupp.prod, Finset.prod_pow_eq_pow_sum]; rfl
  rw [this]; ring

open MvPolynomial Classical in
theorem prm_finrank_map_eq_of_ker {R M N1 N2 : Type*} [Field R] [AddCommGroup M] [Module R M]
    [AddCommGroup N1] [Module R N1] [AddCommGroup N2] [Module R N2] (E : Submodule R M)
    (f : M →ₗ[R] N1) (evS : M →ₗ[R] N2) (hfg : ∀ x, f x = 0 ↔ evS x = 0) :
    Module.finrank R (E.map f) = Module.finrank R (E.map evS) := by
  have kers : LinearMap.ker (f.domRestrict E) = LinearMap.ker (evS.domRestrict E) := by
    ext x; simp only [LinearMap.mem_ker, LinearMap.domRestrict_apply, hfg]
  calc Module.finrank R (E.map f) = Module.finrank R (LinearMap.range (f.domRestrict E)) := by
        rw [LinearMap.range_domRestrict]
    _ = Module.finrank R (E ⧸ LinearMap.ker (f.domRestrict E)) :=
        (LinearMap.quotKerEquivRange _).finrank_eq.symm
    _ = Module.finrank R (E ⧸ LinearMap.ker (evS.domRestrict E)) := by rw [kers]
    _ = Module.finrank R (LinearMap.range (evS.domRestrict E)) :=
        (LinearMap.quotKerEquivRange _).finrank_eq
    _ = Module.finrank R (E.map evS) := by rw [LinearMap.range_domRestrict]

open MvPolynomial Classical in
theorem prm_subcode_transfer (K : Type*) [Field K] [Fintype K] (h t e : ℕ) (he : 1 ≤ e)
    (D : Subspace K (Projectivization K (Fin (h + 1) → K) → K)) (hD : D ≤ prmCode K e h) :
    ∃ D' : Subspace K (Projectivization K (Fin (h + t + 1) → K) → K),
      D' ≤ prmCode K (e + t * (Fintype.card K - 1)) (h + t) ∧
      Module.finrank K D' = Module.finrank K D ∧
      (letI : Fintype (Projectivization K (Fin (h + t + 1) → K)) := Fintype.ofFinite _
       (@Finset.filter _ (fun i => ∃ f ∈ (D' : Set (Projectivization K (Fin (h + t + 1) → K) → K)), f i ≠ 0)
          (fun _ => Classical.propDecidable _) Finset.univ).card) ≤
      (letI : Fintype (Projectivization K (Fin (h + 1) → K)) := Fintype.ofFinite _
       (@Finset.filter _ (fun i => ∃ f ∈ (D : Set (Projectivization K (Fin (h + 1) → K) → K)), f i ≠ 0)
          (fun _ => Classical.propDecidable _) Finset.univ).card) := by
  set q := Fintype.card K with hq
  set e' := e + t * (q - 1) with he'
  have hxhom : ∀ x : homogeneousSubmodule (Fin (h + 1)) K e, x.1.IsHomogeneous e :=
    fun x => (mem_homogeneousSubmodule _ _).mp x.2
  let Λ' : homogeneousSubmodule (Fin (h + 1)) K e →ₗ[K] homogeneousSubmodule (Fin (h + t + 1)) K e' :=
    LinearMap.codRestrict _ ((prmLift K h t q).comp (Submodule.subtype _)) (fun x => by
      rw [mem_homogeneousSubmodule]; exact prmLift_isHomogeneous K h t q e he x.1 (hxhom x))
  set evS := prmEvalMap K e h with hevS
  set f := (prmEvalMap K e' (h + t)).comp Λ' with hf
  set E := D.comap evS with hE
  have hfapply : ∀ x P, f x P = eval P.rep (prmLift K h t q x.1) := fun x P => rfl
  have hgapply : ∀ x P, evS x P = eval P.rep x.1 := fun x P => rfl
  have hLhom : ∀ x : homogeneousSubmodule (Fin (h + 1)) K e,
      (prmLift K h t q x.1).IsHomogeneous e' := fun x => prmLift_isHomogeneous K h t q e he x.1 (hxhom x)
  -- points of the big space with vanishing first coordinates
  have hwne : ∀ P : Projectivization K (Fin (h + t + 1) → K),
      (∀ s : Fin t, P.rep ⟨s, by omega⟩ = 0) →
      (fun j : Fin (h + 1) => P.rep ⟨j + t, by omega⟩) ≠ 0 := by
    intro P hall h0
    apply P.rep_nonzero
    funext j
    by_cases hj : j.val < t
    · exact hall ⟨j, hj⟩
    · have := congrFun h0 ⟨j - t, by omega⟩
      simp only [Pi.zero_apply] at this ⊢
      have e1 : (⟨(⟨j - t, by omega⟩ : Fin (h + 1)).val + t, by omega⟩ : Fin (h + t + 1)) = j := by
        ext; simp; omega
      rw [e1] at this; exact this
  have hker : ∀ x, f x = 0 ↔ evS x = 0 := by
    intro x
    constructor
    · intro hfx
      funext y
      rw [hgapply, Pi.zero_apply]
      set w := y.rep
      let Lw : Fin (h + t + 1) → K := fun j => if hj : t ≤ j.val then w ⟨j - t, by omega⟩ else 0
      have hL0 : ∀ s : Fin t, Lw ⟨s, by omega⟩ = 0 := by
        intro s; simp [Lw]
      have hLσ : (fun j : Fin (h + 1) => Lw ⟨j + t, by omega⟩) = w := by
        funext j; simp [Lw]
      have hLne : Lw ≠ 0 := by
        intro h0
        have hw0 : w = 0 := by rw [← hLσ, h0]; rfl
        exact y.rep_nonzero hw0
      obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep K Lw hLne
      have := congrFun hfx (Projectivization.mk K Lw hLne)
      rw [hfapply, Pi.zero_apply, ← ha, Units.smul_def, prm_isHomogeneous_eval_smul _ (hLhom x),
        prmLift_eval K h t e he x.1 (hxhom x), if_pos hL0, hLσ] at this
      rcases mul_eq_zero.mp this with h1 | h1
      · exact absurd (pow_eq_zero_iff (by omega) |>.mp h1) a.ne_zero
      · exact h1
    · intro hgx
      funext P
      rw [hfapply, Pi.zero_apply, prmLift_eval K h t e he x.1 (hxhom x)]
      split_ifs with hall
      · have hw := hwne P hall
        obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep K _ hw
        have := congrFun hgx (Projectivization.mk K _ hw)
        rw [hgapply, Pi.zero_apply, ← ha, Units.smul_def, prm_isHomogeneous_eval_smul _ (hxhom x)] at this
        rcases mul_eq_zero.mp this with h1 | h1
        · exact absurd (pow_eq_zero_iff (by omega) |>.mp h1) a.ne_zero
        · exact h1
      · rfl
  refine ⟨E.map f, ?_, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact ⟨Λ' x, rfl⟩
  · have hDE : E.map evS = D := Submodule.map_comap_eq_of_le hD
    conv_rhs => rw [← hDE]
    exact prm_finrank_map_eq_of_ker E f evS hker
  · show _ ≤ _
    have hdef : (fun _ : Fin (h + 1) => (1 : K)) ≠ 0 := fun h0 => one_ne_zero (congrFun h0 0)
    let π : Projectivization K (Fin (h + t + 1) → K) → Projectivization K (Fin (h + 1) → K) :=
      fun P => if hw : (fun j : Fin (h + 1) => P.rep ⟨j + t, by omega⟩) ≠ 0 then
        Projectivization.mk K _ hw else Projectivization.mk K _ hdef
    -- a point in the support of the lifted code
    have hsupp : ∀ P, (∃ F ∈ ((E.map f : Subspace K _) : Set (Projectivization K (Fin (h + t + 1) → K) → K)),
        F P ≠ 0) → ∃ x ∈ E, (∀ s : Fin t, P.rep ⟨s, by omega⟩ = 0) ∧
          eval (fun j : Fin (h + 1) => P.rep ⟨j + t, by omega⟩) x.1 ≠ 0 := by
      rintro P ⟨F, ⟨x, hxE, rfl⟩, hFP⟩
      rw [hfapply, prmLift_eval K h t e he x.1 (hxhom x)] at hFP
      split_ifs at hFP with hall
      · exact ⟨x, hxE, hall, hFP⟩
      · exact absurd rfl hFP
    apply Finset.card_le_card_of_injOn π
    · intro P hP
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hP ⊢
      obtain ⟨x, hxE, hall, hval⟩ := hsupp P hP
      have hw := hwne P hall
      have hπ : π P = Projectivization.mk K _ hw := by simp only [π, dif_pos hw]
      refine ⟨evS x, hxE, ?_⟩
      rw [hπ, hgapply]
      obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep K _ hw
      rw [← ha, Units.smul_def, prm_isHomogeneous_eval_smul _ (hxhom x)]
      exact mul_ne_zero (pow_ne_zero _ a.ne_zero) hval
    · intro P1 hP1 P2 hP2 heq
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hP1 hP2
      obtain ⟨x1, -, hall1, -⟩ := hsupp P1 hP1
      obtain ⟨x2, -, hall2, -⟩ := hsupp P2 hP2
      have hw1 := hwne P1 hall1
      have hw2 := hwne P2 hall2
      simp only [π, dif_pos hw1, dif_pos hw2] at heq
      obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff K _ _ hw1 hw2).mp heq
      rw [← Projectivization.mk_rep P1, ← Projectivization.mk_rep P2]
      rw [Projectivization.mk_eq_mk_iff]
      refine ⟨a, ?_⟩
      funext j
      by_cases hj : j.val < t
      · have h1 := hall1 ⟨j, hj⟩
        have h2 := hall2 ⟨j, hj⟩
        simp only [Pi.smul_apply] at h1 h2 ⊢
        rw [Units.smul_def, smul_eq_mul]
        simp only [Fin.eta] at h1 h2
        rw [h1, h2, mul_zero]
      · have := congrFun ha ⟨j - t, by omega⟩
        have e1 : (⟨(⟨j - t, by omega⟩ : Fin (h + 1)).val + t, by omega⟩ : Fin (h + t + 1)) = j := by
          ext; simp; omega
        simp only [Pi.smul_apply] at this ⊢
        rw [e1] at this
        exact this

open MvPolynomial Classical in
theorem prm_exists_subspace_finrank {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (Cs : Submodule K V) [FiniteDimensional K Cs] (r : ℕ) (hr : r ≤ Module.finrank K Cs) :
    ∃ D : Submodule K V, D ≤ Cs ∧ Module.finrank K D = r := by
  let b := Module.finBasis K Cs
  let v : Fin r → V := fun i => (b (Fin.castLE hr i) : V)
  have hli : LinearIndependent K v := by
    have h1 : LinearIndependent K (fun i : Fin r => b (Fin.castLE hr i)) :=
      b.linearIndependent.comp _ (Fin.castLE_injective hr)
    exact h1.map' Cs.subtype (Submodule.ker_subtype Cs)
  refine ⟨Submodule.span K (Set.range v), ?_, ?_⟩
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact (b (Fin.castLE hr i)).2
  · rw [finrank_span_eq_card hli]; simp

/-- Dimension reduction inequality for generalized Hamming weights of projective Reed-Muller codes (Lemma 6.10). -/
theorem prm_ghw_dimension_reduction_le (K : Type*) [Field K] [Fintype K]
    (e m t : ℕ) (he : 1 ≤ e) (hm : 1 ≤ m) (ht : t ≤ m - 1)
    (r : ℕ) (hr1 : 1 ≤ r) (hr2 : r ≤ prmDim K e (m - t)) :
    prmGHW K (e + t * (Fintype.card K - 1)) m r ≤ prmGHW K e (m - t) r := by
  obtain ⟨h, rfl⟩ : ∃ h, m = h + t := ⟨m - t, by omega⟩
  have hh : h + t - t = h := by omega
  rw [hh] at hr2 ⊢
  unfold prmGHW generalizedHammingWeight
  have hfin : FiniteDimensional K (prmCode K e h) := inferInstance
  obtain ⟨D, hDle, hDr⟩ := prm_exists_subspace_finrank (prmCode K e h) r hr2
  have hne : Set.Nonempty { (@Finset.filter _ (fun i => ∃ f ∈ (D : Set (Projectivization K (Fin (h + 1) → K) → K)), f i ≠ 0)
      (fun _ => Classical.propDecidable _) (@Finset.univ _ (Fintype.ofFinite _))).card |
      (D : Subspace K (Projectivization K (Fin (h + 1) → K) → K)) (_ : D ≤ prmCode K e h)
      (_ : Module.finrank K D = r) } := ⟨_, D, hDle, hDr, rfl⟩
  obtain ⟨D0, hD0le, hD0r, hD0eq⟩ := Nat.sInf_mem hne
  obtain ⟨D', hD'le, hD'r, hcard⟩ := prm_subcode_transfer K h t e he D0 hD0le
  rw [← hD0eq]
  refine le_trans (Nat.sInf_le ⟨D', hD'le, by rw [hD'r, hD0r], rfl⟩) hcard
