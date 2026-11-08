import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Physics.LinearPMapIsSelfAdjointRealSmul

/-!
# exists_rank_one_mic_with_invertible_dual

Topic: quantum   Node: d1654b02dbd9

Provenance: helper lemma. arXiv:2610.37347 (Measurement incompatibility and noiseless quantum codes), proof of the main theorem (Eqs. 5-7) and Corollary 1

For every natural number d ≥ 2 there exist g : Fin (d ^ 2) → Fin d → ℂ, real-linear functionals c : Fin (d ^ 2) → (Matrix (Fin d) (Fin d) ℂ →ₗ[ℝ] ℝ), a matrix F : Matrix (Fin d) (Fin d) ℂ and an index i0 : Fin (d ^ 2) such that, writing G i = Matrix.vecMulVec (g i) (star (g i)): ∑ i, G i = 1; c i (G j) = if i = j then 1 else 0 for all i j; every Hermitian X equals ∑ i, c i X • G i (real scalar multiplication); F.IsHermitian and IsUnit F.det; c i0 X = (F * X).trace.re for every Hermitian X; and there is a real s with 1 < s and (1 - s • G i0).PosSemidef. That is, a rank-one minimal informationally complete measurement on C^d with coordinate functionals c, an invertible Hermitian dual operator F for the outcome i0, and G i0 not a projection.
-/

open Matrix in
open scoped ComplexOrder in
theorem posDef_exists_congr_eq_one {d : ℕ} (T : Matrix (Fin d) (Fin d) ℂ) (hT : T.PosDef) :
    ∃ S : Matrix (Fin d) (Fin d) ℂ, S * T * Sᴴ = 1 := by
  set U : Matrix (Fin d) (Fin d) ℂ := (hT.1.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) with hU
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hspec : T = U * diagonal (RCLike.ofReal ∘ hT.1.eigenvalues) * star U := by
    conv_lhs => rw [hT.1.spectral_theorem]
    rfl
  set D : Matrix (Fin d) (Fin d) ℂ := diagonal (fun i => ((Real.sqrt (hT.1.eigenvalues i))⁻¹ : ℂ))
  refine ⟨D * star U, ?_⟩
  have hDH : Dᴴ = D := by
    simp [D, diagonal_conjTranspose]
  rw [hspec, conjTranspose_mul, star_eq_conjTranspose, conjTranspose_conjTranspose, hDH]
  have e : D * Uᴴ * (U * diagonal (RCLike.ofReal ∘ hT.1.eigenvalues) * Uᴴ) * (U * D)
      = D * (Uᴴ * U) * diagonal (RCLike.ofReal ∘ hT.1.eigenvalues) * (Uᴴ * U) * D := by
    simp only [Matrix.mul_assoc]
  rw [← star_eq_conjTranspose] at e ⊢
  rw [e, hUU, Matrix.mul_one, Matrix.mul_one, diagonal_mul_diagonal, diagonal_mul_diagonal]
  rw [← diagonal_one]
  congr 1
  funext i
  have hpos := hT.eigenvalues_pos i
  have hs : Real.sqrt (hT.1.eigenvalues i) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have hsq : ((Real.sqrt (hT.1.eigenvalues i) : ℂ)) * (Real.sqrt (hT.1.eigenvalues i) : ℂ)
      = (hT.1.eigenvalues i : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hpos.le]
  simp only [Function.comp_apply]
  have hs' : (Real.sqrt (hT.1.eigenvalues i) : ℂ) ≠ 0 := by exact_mod_cast hs
  have key : ((Real.sqrt (hT.1.eigenvalues i) : ℂ))⁻¹ * (hT.1.eigenvalues i : ℂ)
      * ((Real.sqrt (hT.1.eigenvalues i) : ℂ))⁻¹ = 1 := by
    rw [← hsq]; field_simp
  exact key

open Matrix in
theorem selfAdjoint_matrix_finrank_le (d : ℕ) :
    FiniteDimensional ℝ (selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) ∧
    Module.finrank ℝ (selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) ≤ d * d := by
  let φ : selfAdjoint (Matrix (Fin d) (Fin d) ℂ) →ₗ[ℝ] (Fin d × Fin d → ℝ) :=
    { toFun := fun X ab => if ab.1 ≤ ab.2 then ((X : Matrix (Fin d) (Fin d) ℂ) ab.1 ab.2).re
        else ((X : Matrix (Fin d) (Fin d) ℂ) ab.1 ab.2).im
      map_add' := by intro X Y; funext ab; simp only [Pi.add_apply]; split_ifs <;> simp
      map_smul' := by intro r X; funext ab; simp only [Pi.smul_apply, RingHom.id_apply]; split_ifs <;> simp }
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro X hX
    have hH : (X : Matrix (Fin d) (Fin d) ℂ)ᴴ = X := X.2
    have h0 : ∀ a b, φ X (a, b) = 0 := fun a b => by rw [hX]; rfl
    apply Subtype.ext
    ext a b
    have hab : ∀ a b, (X : Matrix (Fin d) (Fin d) ℂ) a b = star ((X : Matrix (Fin d) (Fin d) ℂ) b a) := by
      intro a b; have := congrFun (congrFun hH a) b; simp at this; rw [← this]; simp
    simp only [ZeroMemClass.coe_zero, Matrix.zero_apply]
    apply Complex.ext
    · rcases le_or_gt a b with h | h
      · have := h0 a b; simp [φ, h] at this; simpa using this
      · have := h0 b a; simp [φ, h.le] at this; rw [hab]; simpa using this
    · rcases lt_trichotomy a b with h | h | h
      · have := h0 b a; simp [φ, not_le.mpr h] at this; rw [hab]; simp [this]
      · subst h
        have e := hab a a
        have : ((X : Matrix (Fin d) (Fin d) ℂ) a a).im = -((X : Matrix (Fin d) (Fin d) ℂ) a a).im := by
          conv_lhs => rw [e]
          simp
        simp; linarith
      · have := h0 a b; simp [φ, not_le.mpr h] at this; simpa using this
  have hfin : FiniteDimensional ℝ (selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) :=
    Module.Finite.of_injective φ hinj
  refine ⟨hfin, ?_⟩
  have := LinearMap.finrank_le_finrank_of_injective hinj
  simpa [Module.finrank_fintype_fun_eq_card] using this

open Matrix in
open scoped ComplexOrder in
theorem mic_data_of_rank_one_frame {d : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (hcard : Fintype.card ι = d * d) (p : ι → Fin d → ℂ) (i0 : ι) (Q : Matrix (Fin d) (Fin d) ℂ)
    (hli : LinearIndependent ℝ (fun i => vecMulVec (p i) (star (p i))))
    (hQ : Q.IsHermitian) (hQu : IsUnit Q.det)
    (hQP : ∀ i, (Q * vecMulVec (p i) (star (p i))).trace.re = if i = i0 then 1 else 0)
    (hsp : ∀ y : Fin d → ℂ, (∀ i, i ≠ i0 → star (p i) ⬝ᵥ y = 0) → y = 0) :
    ∃ (g : ι → Fin d → ℂ) (c : ι → (Matrix (Fin d) (Fin d) ℂ →ₗ[ℝ] ℝ))
      (F : Matrix (Fin d) (Fin d) ℂ),
      (∑ i, vecMulVec (g i) (star (g i)) = 1) ∧
      (∀ i j, c i (vecMulVec (g j) (star (g j))) = if i = j then 1 else 0) ∧
      (∀ X : Matrix (Fin d) (Fin d) ℂ, X.IsHermitian →
        X = ∑ i, c i X • vecMulVec (g i) (star (g i))) ∧
      F.IsHermitian ∧ IsUnit F.det ∧
      (∀ X : Matrix (Fin d) (Fin d) ℂ, X.IsHermitian → c i0 X = (F * X).trace.re) ∧
      (∃ s : ℝ, 1 < s ∧ (1 - s • vecMulVec (g i0) (star (g i0))).PosSemidef) := by
  classical
  set P : ι → Matrix (Fin d) (Fin d) ℂ := fun i => vecMulVec (p i) (star (p i)) with hPdef
  have hPH : ∀ i, (P i).IsHermitian := fun i => (posSemidef_vecMulVec_self_star (p i)).isHermitian
  -- T positive definite
  set T := ∑ i, P i with hTdef
  have hq : ∀ (v x : Fin d → ℂ), star x ⬝ᵥ (vecMulVec v (star v) *ᵥ x)
      = ((Complex.normSq (star v ⬝ᵥ x) : ℝ) : ℂ) := by
    intro v x
    have h1 : vecMulVec v (star v) *ᵥ x = (star v ⬝ᵥ x) • v := by
      rw [vecMulVec_mulVec]; ext a; simp [mul_comm]
    have h2 : star x ⬝ᵥ v = star (star v ⬝ᵥ x) := by rw [star_dotProduct]
    rw [h1, dotProduct_smul, h2, smul_eq_mul, RCLike.star_def, Complex.mul_conj]
  have hquad : ∀ i (x : Fin d → ℂ), star x ⬝ᵥ (P i *ᵥ x)
      = ((Complex.normSq (star (p i) ⬝ᵥ x) : ℝ) : ℂ) := fun i x => hq (p i) x
  have hTpsd : T.PosSemidef := posSemidef_sum _ fun i _ => posSemidef_vecMulVec_self_star _
  have hT : T.PosDef := by
    rw [posDef_iff_dotProduct_mulVec]
    refine ⟨hTpsd.isHermitian, fun x hx => ?_⟩
    obtain ⟨i, hi, hix⟩ : ∃ i, i ≠ i0 ∧ star (p i) ⬝ᵥ x ≠ 0 := by
      by_contra h
      push Not at h
      exact hx (hsp x h)
    rw [hTdef, sum_mulVec, dotProduct_sum]
    refine Finset.sum_pos' (fun j _ => ?_) ⟨i, Finset.mem_univ _, ?_⟩
    · rw [hquad]; exact Complex.zero_le_real.mpr (Complex.normSq_nonneg _)
    · rw [hquad]; exact Complex.zero_lt_real.mpr (Complex.normSq_pos.mpr hix)
  obtain ⟨S, hS⟩ := posDef_exists_congr_eq_one T hT
  have hSu : IsUnit S.det := isUnit_det_of_right_inverse (B := T * Sᴴ) (by rw [← Matrix.mul_assoc]; exact hS)
  set Sinv := S⁻¹ with hSinv
  have hSS : Sinv * S = 1 := nonsing_inv_mul S hSu
  have hSS' : S * Sinv = 1 := mul_nonsing_inv S hSu
  have hSSH : Sᴴ * Sinvᴴ = 1 := by rw [← conjTranspose_mul, hSS, conjTranspose_one]
  have hSSH' : Sinvᴴ * Sᴴ = 1 := by rw [← conjTranspose_mul, hSS', conjTranspose_one]
  set g : ι → Fin d → ℂ := fun i => S *ᵥ p i with hg
  have hG : ∀ i, vecMulVec (g i) (star (g i)) = S * P i * Sᴴ := by
    intro i
    rw [hg, star_mulVec, hPdef, mul_vecMulVec, vecMulVec_mul]
  have hsumG : ∑ i, vecMulVec (g i) (star (g i)) = 1 := by
    simp only [hG]; rw [← Finset.sum_mul, ← Finset.mul_sum]; exact hS
  -- basis of the Hermitian matrices
  set W := selfAdjoint (Matrix (Fin d) (Fin d) ℂ)
  obtain ⟨hfin, hrk⟩ : FiniteDimensional ℝ W ∧ Module.finrank ℝ W ≤ d * d :=
    selfAdjoint_matrix_finrank_le d
  have hmem : ∀ X : Matrix (Fin d) (Fin d) ℂ, X.IsHermitian → X ∈ W := fun X hX => by
    rw [selfAdjoint.mem_iff]; exact hX
  set Pw : ι → W := fun i => ⟨P i, hmem _ (hPH i)⟩ with hPw
  let val : W →ₗ[ℝ] Matrix (Fin d) (Fin d) ℂ :=
    { toFun := Subtype.val, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hliW : LinearIndependent ℝ Pw := LinearIndependent.of_comp val hli
  have hcardle : Fintype.card ι ≤ Module.finrank ℝ W := hliW.fintype_card_le_finrank
  have hspan := hliW.span_eq_top_of_card_eq_finrank' (by omega)
  set b := Module.Basis.mk hliW (by rw [hspan]) with hb
  have hbi : ∀ i, b i = Pw i := fun i => Module.Basis.mk_apply _ _ _
  have hrep : ∀ (Y : Matrix (Fin d) (Fin d) ℂ) (hY : Y.IsHermitian),
      Y = ∑ i, b.coord i ⟨Y, hmem Y hY⟩ • P i := by
    intro Y hY
    have := congrArg val (b.sum_repr ⟨Y, hmem Y hY⟩)
    rw [map_sum] at this
    simp only [map_smul, hbi] at this
    exact this.symm
  have hcoord : ∀ i j, b.coord i (Pw j) = if i = j then 1 else 0 := by
    intro i j
    rw [← hbi, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    simp [eq_comm]
  let conjL : Matrix (Fin d) (Fin d) ℂ →ₗ[ℝ] Matrix (Fin d) (Fin d) ℂ :=
    (LinearMap.mulLeft ℝ Sinv).comp (LinearMap.mulRight ℝ Sinvᴴ)
  have hconjL : ∀ X, conjL X = Sinv * (X * Sinvᴴ) := fun X => rfl
  have hconjH : ∀ X : Matrix (Fin d) (Fin d) ℂ, X.IsHermitian → (conjL X).IsHermitian := by
    intro X hX
    rw [hconjL, IsHermitian, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
      hX.eq, Matrix.mul_assoc]
  set c : ι → (Matrix (Fin d) (Fin d) ℂ →ₗ[ℝ] ℝ) :=
    fun i => (b.coord i).comp ((selfAdjointPart ℝ).comp conjL) with hc
  have hcH : ∀ i (X : Matrix (Fin d) (Fin d) ℂ) (hX : X.IsHermitian),
      c i X = b.coord i ⟨conjL X, hmem _ (hconjH X hX)⟩ := by
    intro i X hX
    simp only [hc, LinearMap.comp_apply]
    congr 1
    exact IsSelfAdjoint.selfAdjointPart_apply ℝ (hconjH X hX)
  have hconjG : ∀ j, conjL (S * P j * Sᴴ) = P j := by
    intro j
    rw [hconjL, Matrix.mul_assoc, Matrix.mul_assoc, hSSH, Matrix.mul_one, ← Matrix.mul_assoc, hSS,
      Matrix.one_mul]
  have hdualc : ∀ i j, c i (vecMulVec (g j) (star (g j))) = if i = j then 1 else 0 := by
    intro i j
    rw [hG, hcH i _ (by rw [← hG]; exact (posSemidef_vecMulVec_self_star _).isHermitian)]
    have : (⟨conjL (S * P j * Sᴴ), hmem _ (hconjH _ (by rw [← hG]; exact
        (posSemidef_vecMulVec_self_star _).isHermitian))⟩ : W) = Pw j := by
      apply Subtype.ext; exact hconjG j
    rw [this, hcoord]
  refine ⟨g, c, Sinvᴴ * Q * Sinv, hsumG, hdualc, ?_, ?_, ?_, ?_, ?_⟩
  · intro X hX
    have e := hrep (conjL X) (hconjH X hX)
    have eX : X = S * conjL X * Sᴴ := by
      rw [hconjL, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hSS', Matrix.one_mul, Matrix.mul_assoc,
        hSSH', Matrix.mul_one]
    conv_lhs => rw [eX, e]
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hG, hcH i X hX, Matrix.mul_smul, Matrix.smul_mul]
  · rw [IsHermitian, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hQ.eq,
      Matrix.mul_assoc]
  · have h1 : IsUnit Sinv.det := isUnit_nonsing_inv_det S hSu
    have h2 : IsUnit (Sinvᴴ).det := by rw [det_conjTranspose]; exact h1.star
    rw [det_mul, det_mul]; exact (h2.mul hQu).mul h1
  · intro X hX
    rw [hcH i0 X hX]
    have e := hrep (conjL X) (hconjH X hX)
    have htr : (Q * conjL X).trace.re = b.coord i0 ⟨conjL X, hmem _ (hconjH X hX)⟩ := by
      conv_lhs => rw [e]
      rw [Matrix.mul_sum, trace_sum, Complex.re_sum]
      simp only [Matrix.mul_smul, trace_smul, Complex.real_smul, Complex.re_ofReal_mul]
      rw [Finset.sum_eq_single i0]
      · have := hQP i0; simp only [if_true] at this; rw [hPdef]; simp [this]
      · intro j _ hj; have := hQP j; rw [if_neg hj] at this; rw [hPdef]; simp [this]
      · simp
    rw [← htr, hconjL, ← Matrix.mul_assoc, ← Matrix.mul_assoc, trace_mul_comm, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc]
  · set g0 := g i0 with hg0
    -- the norm identity
    have hnorm : star g0 ⬝ᵥ g0 = ((∑ i, Complex.normSq (star (g i) ⬝ᵥ g0) : ℝ) : ℂ) := by
      have e : star g0 ⬝ᵥ ((∑ i, vecMulVec (g i) (star (g i))) *ᵥ g0) = star g0 ⬝ᵥ g0 := by
        rw [hsumG, one_mulVec]
      rw [← e, sum_mulVec, dotProduct_sum]
      push_cast
      exact Finset.sum_congr rfl fun i _ => hq (g i) g0
    set n : ℝ := ∑ i, Complex.normSq (star (g i) ⬝ᵥ g0) with hn
    have hi0 : Complex.normSq (star g0 ⬝ᵥ g0) = n ^ 2 := by
      rw [hnorm, Complex.normSq_ofReal]; ring
    have hy : Sᴴ *ᵥ g0 ≠ 0 := by
      intro h0
      have hg00 : g0 = 0 := by
        have : Sinvᴴ *ᵥ (Sᴴ *ᵥ g0) = g0 := by rw [mulVec_mulVec, hSSH', one_mulVec]
        rw [← this, h0, mulVec_zero]
      have := hdualc i0 i0
      rw [← hg0, hg00] at this
      simp at this
    obtain ⟨i1, hi1, hi1y⟩ : ∃ i, i ≠ i0 ∧ star (p i) ⬝ᵥ (Sᴴ *ᵥ g0) ≠ 0 := by
      by_contra h
      push Not at h
      exact hy (hsp _ h)
    have hgi1 : star (g i1) ⬝ᵥ g0 ≠ 0 := by
      rw [hg, star_mulVec, ← dotProduct_mulVec]; exact hi1y
    have hsplit : n = n ^ 2 + ∑ i ∈ Finset.univ.erase i0, Complex.normSq (star (g i) ⬝ᵥ g0) := by
      have e : n = Complex.normSq (star (g i0) ⬝ᵥ g0) +
          ∑ i ∈ Finset.univ.erase i0, Complex.normSq (star (g i) ⬝ᵥ g0) :=
        (Finset.add_sum_erase _ _ (Finset.mem_univ i0)).symm
      have hf0 : Complex.normSq (star (g i0) ⬝ᵥ g0) = n ^ 2 := hi0
      rw [hf0] at e; exact e
    have hpos1 : 0 < Complex.normSq (star (g i1) ⬝ᵥ g0) := Complex.normSq_pos.mpr hgi1
    have hle1 : Complex.normSq (star (g i1) ⬝ᵥ g0) ≤
        ∑ i ∈ Finset.univ.erase i0, Complex.normSq (star (g i) ⬝ᵥ g0) :=
      Finset.single_le_sum (f := fun i => Complex.normSq (star (g i) ⬝ᵥ g0))
        (fun i _ => Complex.normSq_nonneg _) (Finset.mem_erase.mpr ⟨hi1, Finset.mem_univ _⟩)
    have hn0 : 0 ≤ n := Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
    have hnpos : 0 < n := by nlinarith
    have hnlt : n < 1 := by nlinarith
    refine ⟨1 / n, by rw [lt_div_iff₀ hnpos]; linarith, ?_⟩
    set G0 := vecMulVec g0 (star g0) with hG0
    have hGG : G0 * G0 = n • G0 := by
      rw [hG0, vecMulVec_mul_vecMulVec, hnorm]
      ext a b
      simp [vecMulVec_apply, Complex.real_smul]
      ring
    have hGH : G0ᴴ = G0 := (posSemidef_vecMulVec_self_star g0).isHermitian.eq
    set Pm := 1 - (1 / n) • G0 with hPm
    have hPmH : Pmᴴ = Pm := by
      rw [hPm, conjTranspose_sub, conjTranspose_one, conjTranspose_smul, hGH]; simp
    have hPmP : Pm * Pm = Pm := by
      rw [hPm, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
        Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, hGG, smul_smul, smul_smul]
      have : 1 / n * (1 / n) * n = 1 / n := by field_simp
      rw [this]; abel
    have : Pm = Pmᴴ * Pm := by rw [hPmH, hPmP]
    rw [this]
    exact posSemidef_conjTranspose_mul_self Pm

/-- Coordinates after the first of the rank-one frame vectors (x + u) used to build the MIC of arXiv:2610.37347. -/
noncomputable def mic_frame_tail (m : ℕ) : Option (Fin m × Fin 2 ⊕ Fin m × Fin m) → Fin m → ℂ
  | none => fun _ => 0
  | some (Sum.inl (j, r)) => fun k => if k = j then (if r = 0 then 1 else Complex.I) else 0
  | some (Sum.inr (j, l)) => fun k =>
      if j = l then (if k = j then -1 else 0)
      else (if k = j then 3/5 else 0) + (if k = l then 4/5 * (if j < l then 1 else Complex.I) else 0)

theorem mic_frame_index_card (m : ℕ) :
    Fintype.card (Option (Fin m × Fin 2 ⊕ Fin m × Fin m)) = (m + 1) * (m + 1) := by
  simp [Fintype.card_option, Fintype.card_sum, Fintype.card_prod]; ring

theorem mic_frame_pair_coeff_zero (m : ℕ) (a : Option (Fin m × Fin 2 ⊕ Fin m × Fin m) → ℝ)
    (hE : ∀ x y : Fin m, ∑ i, (a i : ℂ) * (mic_frame_tail m i x * star (mic_frame_tail m i y)) = 0)
    (j l : Fin m) (hjl : j < l) : a (some (Sum.inr (j, l))) = 0 ∧ a (some (Sum.inr (l, j))) = 0 := by
  have hne : j ≠ l := hjl.ne
  have h := hE j l
  rw [Fintype.sum_option, Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_prod_type] at h
  have h1 : ∑ x, ∑ y, (a (some (Sum.inl (x, y))) : ℂ) *
      (mic_frame_tail m (some (Sum.inl (x, y))) j * star (mic_frame_tail m (some (Sum.inl (x, y))) l)) = 0 := by
    refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_
    by_cases hx : j = x
    · subst hx; simp [mic_frame_tail, Ne.symm hne]
    · simp [mic_frame_tail, hx]
  have h2 : ∑ x, ∑ y, (a (some (Sum.inr (x, y))) : ℂ) *
      (mic_frame_tail m (some (Sum.inr (x, y))) j * star (mic_frame_tail m (some (Sum.inr (x, y))) l))
      = (a (some (Sum.inr (j, l))) : ℂ) * (12/25) + (a (some (Sum.inr (l, j))) : ℂ) * (12/25 * Complex.I) := by
    rw [← Fintype.sum_prod_type' (f := fun x y => (a (some (Sum.inr (x, y))) : ℂ) *
      (mic_frame_tail m (some (Sum.inr (x, y))) j * star (mic_frame_tail m (some (Sum.inr (x, y))) l)))]
    rw [Fintype.sum_eq_add (j, l) (l, j) (by simp [hne])]
    · simp [mic_frame_tail, hne, Ne.symm hne, hjl, not_lt.mpr hjl.le]; ring
    · rintro ⟨x, y⟩ ⟨h1, h2⟩
      have h1' : ¬ (x = j ∧ y = l) := fun ⟨e1, e2⟩ => h1 (by rw [e1, e2])
      have h2' : ¬ (x = l ∧ y = j) := fun ⟨e1, e2⟩ => h2 (by rw [e1, e2])
      dsimp only
      simp only [mic_frame_tail]
      by_cases hxy : x = y
      · subst hxy; by_cases hjx : j = x
        · subst hjx; simp [hne, Ne.symm hne]
        · simp [hjx]
      · simp only [hxy, if_false]
        by_cases hjx : j = x
        · subst hjx
          have hly : l ≠ y := fun e => h1' ⟨rfl, e.symm⟩
          simp [Ne.symm hne, hly]
        · by_cases hjy : j = y
          · subst hjy
            have hlx : l ≠ x := fun e => h2' ⟨e.symm, rfl⟩
            simp [hjx, hlx, Ne.symm hne]
          · simp [hjx, hjy]
  rw [h1, h2] at h
  simp [mic_frame_tail] at h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp at hre him
  constructor <;> linarith

open Matrix in
theorem mic_frame_linearIndependent (m : ℕ) : LinearIndependent ℝ (fun i : Option (Fin m × Fin 2 ⊕ Fin m × Fin m) =>
    vecMulVec (Fin.cons (1 : ℂ) (mic_frame_tail m i) : Fin (m + 1) → ℂ)
      (star (Fin.cons (1 : ℂ) (mic_frame_tail m i) : Fin (m + 1) → ℂ))) := by
  rw [Fintype.linearIndependent_iff]
  intro a ha
  have hE0 : ∀ x y : Fin (m + 1), ∑ i, (a i : ℂ) * ((Fin.cons (1 : ℂ) (mic_frame_tail m i) : Fin (m + 1) → ℂ) x
      * star ((Fin.cons (1 : ℂ) (mic_frame_tail m i) : Fin (m + 1) → ℂ) y)) = 0 := by
    intro x y
    have := congrFun (congrFun ha x) y
    simpa only [Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, Complex.real_smul,
      Matrix.zero_apply, Pi.star_apply] using this
  have hE : ∀ x y : Fin m, ∑ i, (a i : ℂ) * (mic_frame_tail m i x * star (mic_frame_tail m i y)) = 0 := by
    intro x y; simpa using hE0 x.succ y.succ
  have hpair : ∀ j l, j ≠ l → a (some (Sum.inr (j, l))) = 0 := by
    intro j l hjl
    rcases lt_or_gt_of_ne hjl with h | h
    · exact (mic_frame_pair_coeff_zero m a hE j l h).1
    · exact (mic_frame_pair_coeff_zero m a hE l j h).2
  have hinr : ∀ (F : Fin m → Fin m → ℂ),
      ∑ x, ∑ y, (a (some (Sum.inr (x, y))) : ℂ) * F x y = ∑ x, (a (some (Sum.inr (x, x))) : ℂ) * F x x := by
    intro F
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_eq_single x]
    · intro y _ hyx; rw [hpair x y (Ne.symm hyx)]; simp
    · simp
  have hdiag : ∀ j, a (some (Sum.inl (j, 0))) = 0 ∧ a (some (Sum.inl (j, 1))) = 0 ∧
      a (some (Sum.inr (j, j))) = 0 := by
    intro j
    have e1 := hE0 0 j.succ
    have e2 := hE j j
    rw [Fintype.sum_option, Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_prod_type] at e1 e2
    simp only [Fin.cons_zero, Fin.cons_succ, one_mul] at e1
    rw [hinr] at e1 e2
    simp [mic_frame_tail, Fin.sum_univ_two] at e1 e2
    simp only [apply_ite (starRingEnd ℂ), map_zero, map_neg, map_one, Complex.conj_I, mul_ite,
      mul_zero, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true] at e1
    have hre := congrArg Complex.re e1
    have him := congrArg Complex.im e1
    have hre2 := congrArg Complex.re e2
    simp at hre him hre2
    refine ⟨by linarith, by linarith, by linarith⟩
  have hnone : a none = 0 := by
    have e := hE0 0 0
    rw [Fintype.sum_option, Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_prod_type] at e
    rw [hinr] at e
    have : ∀ x (r : Fin 2), a (some (Sum.inl (x, r))) = 0 := by
      intro x r; fin_cases r
      · exact (hdiag x).1
      · exact (hdiag x).2.1
    simp [this, (fun x => (hdiag x).2.2)] at e
    exact e
  intro i
  rcases i with _ | ⟨⟨j, r⟩⟩ | ⟨⟨j, l⟩⟩
  · exact hnone
  · fin_cases r
    · exact (hdiag j).1
    · exact (hdiag j).2.1
  · by_cases hjl : j = l
    · subst hjl; exact (hdiag j).2.2
    · exact hpair j l hjl

open Matrix in
theorem mic_frame_tail_normSq (m : ℕ) (i : Option (Fin m × Fin 2 ⊕ Fin m × Fin m)) (hi : i ≠ none) :
    ∑ k, Complex.normSq (mic_frame_tail m i k) = 1 := by
  rcases i with _ | ⟨⟨j, r⟩⟩ | ⟨⟨j, l⟩⟩
  · exact absurd rfl hi
  · rw [Finset.sum_eq_single j]
    · fin_cases r <;> simp [mic_frame_tail]
    · intro k _ hk; simp [mic_frame_tail, hk]
    · simp
  · by_cases hjl : j = l
    · subst hjl
      rw [Finset.sum_eq_single j]
      · simp [mic_frame_tail]
      · intro k _ hk; simp [mic_frame_tail, hk]
      · simp
    · rw [Fintype.sum_eq_add j l hjl]
      · rcases lt_or_gt_of_ne hjl with h | h
        · simp [mic_frame_tail, hjl, Ne.symm hjl, h, Complex.normSq_apply]; norm_num
        · simp [mic_frame_tail, hjl, Ne.symm hjl, h, not_lt.mpr h.le, Complex.normSq_apply]; norm_num
      · rintro k ⟨h1, h2⟩; simp [mic_frame_tail, hjl, h1, h2]

open scoped ComplexOrder in
theorem exists_rank_one_mic_with_invertible_dual (d : ℕ) (hd : 2 ≤ d) :
    ∃ (g : Fin (d ^ 2) → Fin d → ℂ) (c : Fin (d ^ 2) → (Matrix (Fin d) (Fin d) ℂ →ₗ[ℝ] ℝ))
      (F : Matrix (Fin d) (Fin d) ℂ) (i0 : Fin (d ^ 2)),
      (∑ i, Matrix.vecMulVec (g i) (star (g i)) = 1) ∧
      (∀ i j, c i (Matrix.vecMulVec (g j) (star (g j))) = if i = j then 1 else 0) ∧
      (∀ X : Matrix (Fin d) (Fin d) ℂ, X.IsHermitian →
        X = ∑ i, c i X • Matrix.vecMulVec (g i) (star (g i))) ∧
      F.IsHermitian ∧ IsUnit F.det ∧
      (∀ X : Matrix (Fin d) (Fin d) ℂ, X.IsHermitian → c i0 X = (F * X).trace.re) ∧
      (∃ s : ℝ, 1 < s ∧ (1 - s • Matrix.vecMulVec (g i0) (star (g i0))).PosSemidef) := open Matrix in by
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  have hm : 0 < m := by omega
  set p : Option (Fin m × Fin 2 ⊕ Fin m × Fin m) → Fin (m + 1) → ℂ :=
    fun i => Fin.cons (1 : ℂ) (mic_frame_tail m i) with hp
  set Q : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ := diagonal (Fin.cons (1 : ℂ) (fun _ => -1)) with hQ
  have hQH : Q.IsHermitian := by
    rw [hQ, IsHermitian, diagonal_conjTranspose]
    congr 1
    funext a
    refine Fin.cases ?_ (fun k => ?_) a <;> simp
  have hQQ : Q * Q = 1 := by
    rw [hQ, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext a
    refine Fin.cases ?_ (fun k => ?_) a <;> simp
  have hQu : IsUnit Q.det := isUnit_det_of_right_inverse hQQ
  have hQP : ∀ i, (Q * vecMulVec (p i) (star (p i))).trace.re = if i = none then 1 else 0 := by
    intro i
    have e : (Q * vecMulVec (p i) (star (p i))).trace.re = 1 - ∑ k, Complex.normSq (mic_frame_tail m i k) := by
      rw [hQ, trace, Complex.re_sum, Fin.sum_univ_succ]
      simp [diagonal_mul, vecMulVec_apply, hp, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      simp [← Complex.ofReal_pow]
      ring
    rw [e]
    by_cases hi : i = none
    · subst hi; simp [mic_frame_tail]
    · rw [mic_frame_tail_normSq m i hi, if_neg hi]; ring
  have hsp : ∀ y : Fin (m + 1) → ℂ, (∀ i, i ≠ none → star (p i) ⬝ᵥ y = 0) → y = 0 := by
    intro y hy
    have hdot : ∀ i, star (p i) ⬝ᵥ y = y 0 + ∑ k, star (mic_frame_tail m i k) * y k.succ := by
      intro i; simp [dotProduct, Fin.sum_univ_succ, hp]
    have hk : ∀ k : Fin m, y 0 + y k.succ = 0 := by
      intro k
      have := hy (some (Sum.inl (k, 0))) (by simp)
      rw [hdot, Finset.sum_eq_single k] at this
      · simpa [mic_frame_tail] using this
      · intro k' _ hk'; simp [mic_frame_tail, hk']
      · simp
    have hk' : ∀ k : Fin m, y 0 - y k.succ = 0 := by
      intro k
      have := hy (some (Sum.inr (k, k))) (by simp)
      rw [hdot, Finset.sum_eq_single k] at this
      · simp [mic_frame_tail] at this; linear_combination this
      · intro k' _ hk'; simp [mic_frame_tail, hk']
      · simp
    have h0 : y 0 = 0 := by
      have a1 := hk ⟨0, hm⟩
      have a2 := hk' ⟨0, hm⟩
      linear_combination (a1 + a2) / 2
    funext a
    refine Fin.cases h0 (fun k => ?_) a
    have := hk k
    rw [h0, zero_add] at this
    exact this
  have hcard := mic_frame_index_card m
  obtain ⟨g, c, F, h1, h2, h3, h4, h5, h6, h7⟩ :=
    mic_data_of_rank_one_frame hcard p none Q (mic_frame_linearIndependent m) hQH hQu hQP hsp
  let eι := Fintype.equivFinOfCardEq
    (show Fintype.card (Option (Fin m × Fin 2 ⊕ Fin m × Fin m)) = (m + 1) ^ 2 by rw [hcard]; ring)
  refine ⟨fun k => g (eι.symm k), fun k => c (eι.symm k), F, eι none, ?_, ?_, ?_, h4, h5, ?_, ?_⟩
  · rw [← h1]; exact eι.symm.sum_comp (fun i => vecMulVec (g i) (star (g i)))
  · intro i j; rw [h2]; simp [eι.symm.injective.eq_iff]
  · intro X hX
    conv_lhs => rw [h3 X hX]
    exact (eι.symm.sum_comp (fun i => c i X • vecMulVec (g i) (star (g i)))).symm
  · intro X hX; simp only [Equiv.symm_apply_apply]; exact h6 X hX
  · simpa using h7
