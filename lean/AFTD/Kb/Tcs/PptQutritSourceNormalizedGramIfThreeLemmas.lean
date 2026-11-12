import AFTD.Prelude
import AFTD.Kb.Tcs.PptQutritBellState
import AFTD.Kb.Tcs.PptQutritSteeredNormalizer
import AFTD.Kb.Tcs.PptQutritBellVector
import AFTD.Kb.Tcs.F

/-!
# ppt_qutrit_source_normalized_gram_if_three_lemmas

Topic: quantum   Node: fc5441d4e11f

Provenance: helper lemma. Source-specific helper for OP-693, based on https://arxiv.org/abs/1405.4502.

The explicit source has a normalized PPT-invariant Gram factor on every rank-two projection, conditional on basis selection, source partial-transpose invariance, and real positive-block normalization.
-/

open Matrix
open scoped BigOperators Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
private lemma in767_actualnorm_ppt_under_second_factor
    {n m : ℕ} (ρ : Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ)
    (W : Matrix (Fin n) (Fin m) ℂ)
    (hpt : ∀ a c : Fin 3, ∀ x y : Fin n, ρ (a,x) (c,y) = ρ (c,x) (a,y)) :
    ∀ a c : Fin 3, ∀ p q : Fin m,
      (∑ x : Fin n, ∑ y : Fin n, star (W x p) * ρ (a,x) (c,y) * W y q) =
      ∑ x : Fin n, ∑ y : Fin n, star (W x p) * ρ (c,x) (a,y) * W y q := by
  intro a c p q
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  rw [hpt a c x y]

private lemma in767_actualnorm_ppt_under_real_first_filter
    {m : ℕ} (ρ : Matrix (Fin 3 × Fin m) (Fin 3 × Fin m) ℂ)
    (H : Matrix (Fin 3) (Fin 3) ℂ)
    (hpt : ∀ i j : Fin 3, ∀ p q : Fin m, ρ (i,p) (j,q) = ρ (j,p) (i,q)) :
    ∀ a c : Fin 3, ∀ p q : Fin m,
      (∑ i : Fin 3, ∑ j : Fin 3, H a i * ρ (i,p) (j,q) * H c j) =
      ∑ i : Fin 3, ∑ j : Fin 3, H c i * ρ (i,p) (j,q) * H a j := by
  intro a c p q
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hpt i j p q]
  ring


private lemma in767_actualnorm_pt_hermitian_blocks
    (X : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ) (hX : X.IsHermitian)
    (hpt : ∀ i j : Fin 3, ∀ p q : Fin 2, X (i,p) (j,q) = X (j,p) (i,q)) :
    (let B : Matrix (Fin 3) (Fin 3) ℂ := fun i j => X (i,0) (j,1); B.transpose = B) ∧
    (∀ i j : Fin 3, ∀ p : Fin 2, star (X (i,p) (j,p)) = X (i,p) (j,p)) := by
  constructor
  · ext i j
    exact hpt j i 0 1
  · intro i j p
    calc
      star (X (i,p) (j,p)) = X (j,p) (i,p) := hX.apply (j,p) (i,p)
      _ = X (i,p) (j,p) := hpt j i p p

private lemma in767_actualnorm_bipartite_product_congruence
    (T : Matrix (Fin 3) (Fin 3) ℂ) (v : Fin 4 → Fin 3 → ℂ) (z : Fin 4 → Fin 2 → ℂ)
    (i j : Fin 3) (p q : Fin 2) :
    (∑ a : Fin 3, ∑ b : Fin 3, T i a *
      (∑ t : Fin 4, (v t a * z t p) * star (v t b * z t q)) * star (T j b)) =
      ∑ t : Fin 4, ((T *ᵥ v t) i * z t p) * star ((T *ᵥ v t) j * z t q) := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_four, star_mul, star_sum]
  ring


private lemma in767_actualnorm_four_column_gram_congruence
    (T : Matrix (Fin 3) (Fin 3) ℂ) (F : Matrix (Fin 3 × Fin 2) (Fin 4) ℂ)
    (i j : Fin 3) (p q : Fin 2) :
    (∑ t : Fin 4, (∑ a : Fin 3, T i a * F (a,p) t) *
      star (∑ b : Fin 3, T j b * F (b,q) t)) =
      ∑ a : Fin 3, ∑ b : Fin 3, T i a * (F*Fᴴ) (a,p) (b,q) * star (T j b) := by
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_three, Fin.sum_univ_four, star_mul]
  ring

private lemma in767_actualnorm_normalize_pt_gram_factor
    (G : Matrix (Fin 3 × Fin 2) (Fin 4) ℂ)
    (hpt : ∀ i j : Fin 3, ∀ p q : Fin 2, (G*Gᴴ) (i,p) (j,q) = (G*Gᴴ) (j,p) (i,q))
    (hpos : (let U : Matrix (Fin 3) (Fin 4) ℂ := fun i t => G (i,0) t
      let R : Matrix (Fin 3) (Fin 3) ℝ := fun i j => ((U*Uᴴ) i j).re
      R.PosDef))
    (hnorm : ∀ R : Matrix (Fin 3) (Fin 3) ℝ, R.PosDef →
      ∃ H : Matrix (Fin 3) (Fin 3) ℝ, H.transpose = H ∧ IsUnit H ∧ H*R*H = 1) :
    ∃ (F : Matrix (Fin 3 × Fin 2) (Fin 4) ℂ) (T : Matrix (Fin 3) (Fin 3) ℂ),
      (let U : Matrix (Fin 3) (Fin 4) ℂ := fun i t => F (i,0) t; U*Uᴴ = 1) ∧
      (∀ i j : Fin 3, ∀ p q : Fin 2, (F*Fᴴ) (i,p) (j,q) = (F*Fᴴ) (j,p) (i,q)) ∧
      (∀ i : Fin 3, ∀ p : Fin 2, ∀ t : Fin 4, G (i,p) t = ∑ a : Fin 3, T i a * F (a,p) t) := by
  let U0 : Matrix (Fin 3) (Fin 4) ℂ := fun i t => G (i,0) t
  let C : Matrix (Fin 3) (Fin 3) ℂ := U0*U0ᴴ
  let R : Matrix (Fin 3) (Fin 3) ℝ := fun i j => (C i j).re
  have hX : (G*Gᴴ).IsHermitian := Matrix.isHermitian_mul_conjTranspose_self G
  obtain ⟨_, hreal⟩ := in767_actualnorm_pt_hermitian_blocks (G*Gᴴ) hX hpt
  have hCreal : ∀ i j, star (C i j) = C i j := by
    intro i j
    simpa [C, U0, Matrix.mul_apply, Matrix.conjTranspose_apply] using hreal i j 0
  have hR : R.map (algebraMap ℝ ℂ) = C := by
    ext i j
    have hh := hCreal i j
    apply Complex.ext <;> simp [R, Complex.ext_iff] at hh ⊢ <;> linarith
  obtain ⟨H, hHsym, hHunit, hH⟩ := hnorm R hpos
  obtain ⟨Hu, hHu⟩ := hHunit
  let J : Matrix (Fin 3) (Fin 3) ℝ := ↑(Hu⁻¹)
  have hJH : J * H = 1 := by
    rw [← hHu]
    exact Units.inv_mul Hu
  let E : Matrix (Fin 3) (Fin 3) ℂ := H.map (algebraMap ℝ ℂ)
  let D : Matrix (Fin 3) (Fin 3) ℂ := J.map (algebraMap ℝ ℂ)
  have hDE : D * E = 1 := by
    have hh := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M.map (algebraMap ℝ ℂ)) hJH
    simp only [Matrix.map_mul, Matrix.map_one, map_zero, map_one] at hh
    exact hh
  have hEreal : ∀ i j, star (E i j) = E i j := by intro i j; simp [E]
  have hEherm : Eᴴ = E := by
    ext i j
    have hh := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M i j) hHsym
    simpa [E, Matrix.conjTranspose_apply, Matrix.transpose_apply] using congrArg (algebraMap ℝ ℂ) hh
  have hEC : E*C*E = 1 := by
    have hh := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M.map (algebraMap ℝ ℂ)) hH
    simp only [Matrix.map_mul, Matrix.map_one, map_zero, map_one] at hh
    change E * (R.map (algebraMap ℝ ℂ)) * E = 1 at hh
    rw [hR] at hh
    exact hh
  let F : Matrix (Fin 3 × Fin 2) (Fin 4) ℂ := fun ip t => ∑ i : Fin 3, E ip.1 i * G (i,ip.2) t
  let U : Matrix (Fin 3) (Fin 4) ℂ := fun i t => F (i,0) t
  have hUF : U = E*U0 := by ext i t; simp [U, F, U0, Matrix.mul_apply]
  refine ⟨F, D, ?_, ?_, ?_⟩
  · change U * Uᴴ = 1
    rw [hUF, Matrix.conjTranspose_mul, hEherm]
    simpa [C, Matrix.mul_assoc] using hEC
  · intro i j p q
    have hcongr (i j : Fin 3) (p q : Fin 2) : (F*Fᴴ) (i,p) (j,q) =
        ∑ a : Fin 3, ∑ b : Fin 3, E i a * (G*Gᴴ) (a,p) (b,q) * E j b := by
      change (∑ t : Fin 4, (∑ a : Fin 3, E i a * G (a,p) t) *
        star (∑ b : Fin 3, E j b * G (b,q) t)) = _
      rw [in767_actualnorm_four_column_gram_congruence]
      simp only [hEreal]
    rw [hcongr, hcongr]
    exact in767_actualnorm_ppt_under_real_first_filter (G*Gᴴ) E hpt i j p q
  · intro i p t
    let Y : Matrix (Fin 3) (Fin 4) ℂ := fun j t => G (j,p) t
    change Y i t = (D * (E * Y)) i t
    rw [← Matrix.mul_assoc, hDE, Matrix.one_mul]


private lemma in767_actualnorm_real_gram_positive
    (U : Matrix (Fin 3) (Fin 4) ℂ) (hinj : Function.Injective U.vecMul) :
    (let R : Matrix (Fin 3) (Fin 3) ℝ := fun i j => ((U*Uᴴ) i j).re; R.PosDef) := by
  let C : Matrix (Fin 3) (Fin 3) ℂ := U*Uᴴ
  let R : Matrix (Fin 3) (Fin 3) ℝ := fun i j => (C i j).re
  have hC : C.PosDef := Matrix.PosDef.mul_conjTranspose_self U hinj
  have hRherm : R.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    have hh := congrArg Complex.re (hC.isHermitian.apply i j)
    simpa [R, C] using hh
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hRherm
  intro x hx
  let xc : Fin 3 → ℂ := fun i => x i
  have hxc : xc ≠ 0 := by
    intro h
    apply hx
    ext i
    have hh := congrFun h i
    change (x i : ℂ) = 0 at hh
    exact_mod_cast hh
  have hp := (Complex.pos_iff.mp (hC.dotProduct_mulVec_pos hxc)).1
  have heq : star x ⬝ᵥ (R *ᵥ x) = (star xc ⬝ᵥ (C *ᵥ xc)).re := by
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three, Complex.mul_re, R, xc]
  rw [heq]
  exact hp

private lemma in767_actualnorm_full_row_rank_vecmul_injective
    (U : Matrix (Fin 3) (Fin 4) ℂ) (hrank : U.rank = 3) : Function.Injective U.vecMul := by
  let f := U.transpose.mulVecLin
  have hdim : Module.finrank ℂ (Fin 3 → ℂ) = 3 := by simp [Module.finrank_pi]
  have hrange : Module.finrank ℂ (LinearMap.range f) = 3 := by
    change U.transpose.rank = 3
    rw [Matrix.rank_transpose]
    exact hrank
  have hk := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange, hdim] at hk
  have hker : LinearMap.ker f = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
  have hf : Function.Injective f := LinearMap.ker_eq_bot.mp hker
  intro x y h
  apply hf
  simpa [f, Matrix.mulVec_transpose] using h


private lemma in767_actualnorm_normalize_pt_gram_factor_of_rank
    (G : Matrix (Fin 3 × Fin 2) (Fin 4) ℂ)
    (hpt : ∀ i j : Fin 3, ∀ p q : Fin 2, (G*Gᴴ) (i,p) (j,q) = (G*Gᴴ) (j,p) (i,q))
    (hrank : (let U : Matrix (Fin 3) (Fin 4) ℂ := fun i t => G (i,0) t; U.rank = 3))
    (hnorm : ∀ R : Matrix (Fin 3) (Fin 3) ℝ, R.PosDef →
      ∃ H : Matrix (Fin 3) (Fin 3) ℝ, H.transpose = H ∧ IsUnit H ∧ H*R*H = 1) :
    ∃ (F : Matrix (Fin 3 × Fin 2) (Fin 4) ℂ) (T : Matrix (Fin 3) (Fin 3) ℂ),
      (let U : Matrix (Fin 3) (Fin 4) ℂ := fun i t => F (i,0) t; U*Uᴴ = 1) ∧
      (∀ i j : Fin 3, ∀ p q : Fin 2, (F*Fᴴ) (i,p) (j,q) = (F*Fᴴ) (j,p) (i,q)) ∧
      (∀ i : Fin 3, ∀ p : Fin 2, ∀ t : Fin 4, G (i,p) t = ∑ a : Fin 3, T i a * F (a,p) t) := by
  let U : Matrix (Fin 3) (Fin 4) ℂ := fun i t => G (i,0) t
  have hinj : Function.Injective U.vecMul := in767_actualnorm_full_row_rank_vecmul_injective U hrank
  have hpos := in767_actualnorm_real_gram_positive U hinj
  exact in767_actualnorm_normalize_pt_gram_factor G hpt hpos hnorm


private lemma in767_actualnorm_compressed_rankfour_gram
    (v : Fin 4 → Fin 3 × Fin 3 → ℂ) (lam : Fin 4 → ℝ)
    (W : Matrix (Fin 3) (Fin 2) ℂ) (hlam : ∀ t, 0 ≤ lam t)
    (i j : Fin 3) (p q : Fin 2) :
    (∑ x : Fin 3, ∑ y : Fin 3, star (W x p) *
      (∑ t : Fin 4, (lam t : ℂ) * v t (i,x) * star (v t (j,y))) * W y q) =
    ∑ t : Fin 4,
      ((Real.sqrt (lam t) : ℂ) * ∑ x : Fin 3, star (W x p) * v t (i,x)) *
      star ((Real.sqrt (lam t) : ℂ) * ∑ y : Fin 3, star (W y q) * v t (j,y)) := by
  have hsq (t : Fin 4) : (Real.sqrt (lam t) : ℂ)^2 = (lam t : ℂ) := by
    exact_mod_cast Real.sq_sqrt (hlam t)
  simp [Fin.sum_univ_three, Fin.sum_univ_four, star_mul, star_add]
  ring_nf
  simp only [hsq]
  ring


private lemma in767_actualnorm_source_compressed_gram_normalization
    (source : Fin 4 → Fin 3 × Fin 3 → ℂ) (lam : Fin 4 → ℝ) (W : Matrix (Fin 3) (Fin 2) ℂ)
    (hlam : ∀ t, 0 ≤ lam t)
    (hsourcept : ∀ i j x y : Fin 3,
      (∑ t : Fin 4, (lam t : ℂ) * source t (i,x) * star (source t (j,y))) =
      ∑ t : Fin 4, (lam t : ℂ) * source t (j,x) * star (source t (i,y)))
    (hrank : (let U : Matrix (Fin 3) (Fin 4) ℂ := fun i t =>
      (Real.sqrt (lam t) : ℂ) * (∑ x : Fin 3, star (W x 0) * source t (i,x)); U.rank=3))
    (hnorm : ∀ R : Matrix (Fin 3) (Fin 3) ℝ, R.PosDef →
      ∃ H : Matrix (Fin 3) (Fin 3) ℝ, H.transpose = H ∧ IsUnit H ∧ H*R*H = 1) :
    ∃ (F : Matrix (Fin 3 × Fin 2) (Fin 4) ℂ) (T : Matrix (Fin 3) (Fin 3) ℂ),
      (let U : Matrix (Fin 3) (Fin 4) ℂ := fun i t => F (i,0) t; U*Uᴴ = 1) ∧
      (∀ i j : Fin 3, ∀ p q : Fin 2, (F*Fᴴ) (i,p) (j,q) = (F*Fᴴ) (j,p) (i,q)) ∧
      (∀ i : Fin 3, ∀ p : Fin 2, ∀ t : Fin 4,
        (Real.sqrt (lam t) : ℂ) * (∑ x : Fin 3, star (W x p) * source t (i,x)) =
        ∑ a : Fin 3, T i a * F (a,p) t) := by
  let G : Matrix (Fin 3 × Fin 2) (Fin 4) ℂ := fun ip t =>
    (Real.sqrt (lam t) : ℂ) * (∑ x : Fin 3, star (W x ip.2) * source t (ip.1,x))
  let ρ : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ := fun ax cy =>
    ∑ t : Fin 4, (lam t : ℂ) * source t ax * star (source t cy)
  have hGpt : ∀ i j : Fin 3, ∀ p q : Fin 2, (G*Gᴴ) (i,p) (j,q) = (G*Gᴴ) (j,p) (i,q) := by
    intro i j p q
    have hi := (in767_actualnorm_compressed_rankfour_gram source lam W hlam i j p q).symm
    have hj := (in767_actualnorm_compressed_rankfour_gram source lam W hlam j i p q).symm
    change (G*Gᴴ) (i,p) (j,q) = _ at hi
    change (G*Gᴴ) (j,p) (i,q) = _ at hj
    rw [hi, hj]
    exact in767_actualnorm_ppt_under_second_factor ρ W hsourcept i j p q
  exact in767_actualnorm_normalize_pt_gram_factor_of_rank G hGpt hrank hnorm

theorem ppt_qutrit_source_normalized_gram_if_three_lemmas
    (hselect :   ∀ P : Matrix (Fin 3) (Fin 3) ℂ, P.IsHermitian → P*P=P → P.rank=2 →
    ∃ U : Matrix (Fin 3) (Fin 2) ℂ,
      Uᴴ*U=1 ∧ U*Uᴴ=P ∧
      (let W : Matrix (Fin 3) (Fin 2) ℂ := ppt_qutrit_steered_normalizer * U
       let lam : Fin 4 → ℝ := fun t => if t = 0 then 3257/6884 else if t = 3 then 27/6884 else 450/1721
       let G : Matrix (Fin 3) (Fin 4) ℂ := fun i t =>
        (Real.sqrt (lam t) : ℂ) * (∑ x : Fin 3, star (W x 0) * ppt_qutrit_bell_vector t (i,x))
       G.rank=3))
    (hstate : ∀ i x j y : Fin 3,
      ppt_qutrit_bell_state (i,x) (j,y) = ppt_qutrit_bell_state (j,x) (i,y))
    (hnorm : ∀ R : Matrix (Fin 3) (Fin 3) ℝ, R.PosDef →
      ∃ H : Matrix (Fin 3) (Fin 3) ℝ, H.transpose = H ∧ IsUnit H ∧ H*R*H = 1) :
  ∀ P : Matrix (Fin 3) (Fin 3) ℂ, P.IsHermitian → P*P=P → P.rank=2 →
    ∃ (U : Matrix (Fin 3) (Fin 2) ℂ) (F : Matrix (Fin 3 × Fin 2) (Fin 4) ℂ)
      (T : Matrix (Fin 3) (Fin 3) ℂ),
      Uᴴ*U=1 ∧ U*Uᴴ=P ∧
      (let V : Matrix (Fin 3) (Fin 4) ℂ := fun i t => F (i,0) t; V*Vᴴ=1) ∧
      (∀ i j : Fin 3, ∀ p q : Fin 2, (F*Fᴴ) (i,p) (j,q) = (F*Fᴴ) (j,p) (i,q)) ∧
      (let W : Matrix (Fin 3) (Fin 2) ℂ := ppt_qutrit_steered_normalizer * U
       let lam : Fin 4 → ℝ := fun t => if t = 0 then 3257/6884 else if t = 3 then 27/6884 else 450/1721
       ∀ i : Fin 3, ∀ p : Fin 2, ∀ t : Fin 4,
        (Real.sqrt (lam t) : ℂ) * (∑ x : Fin 3, star (W x p) * ppt_qutrit_bell_vector t (i,x)) =
          ∑ a : Fin 3, T i a * F (a,p) t) := by
  intro P hP hPP hRank
  obtain ⟨U, hU, hUP, hfull⟩ := hselect P hP hPP hRank
  let W : Matrix (Fin 3) (Fin 2) ℂ := ppt_qutrit_steered_normalizer * U
  let lam : Fin 4 → ℝ := fun t => if t = 0 then 3257/6884 else if t = 3 then 27/6884 else 450/1721
  have hlam : ∀ t, 0 ≤ lam t := by
    intro t
    dsimp [lam]
    split_ifs <;> norm_num
  have hpt : ∀ i j x y : Fin 3,
      (∑ t : Fin 4, (lam t : ℂ) * ppt_qutrit_bell_vector t (i,x) * star (ppt_qutrit_bell_vector t (j,y))) =
      ∑ t : Fin 4, (lam t : ℂ) * ppt_qutrit_bell_vector t (j,x) * star (ppt_qutrit_bell_vector t (i,y)) := by
    intro i j x y
    have hh := hstate i x j y
    simpa [ppt_qutrit_bell_state, lam, Fin.sum_univ_four, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.vecMulVec_apply, Pi.star_apply, Complex.real_smul, mul_assoc] using hh
  obtain ⟨F, T, hupper, hptF, hrel⟩ :=
    in767_actualnorm_source_compressed_gram_normalization ppt_qutrit_bell_vector lam W hlam hpt hfull hnorm
  exact ⟨U, F, T, hU, hUP, hupper, hptF, hrel⟩
