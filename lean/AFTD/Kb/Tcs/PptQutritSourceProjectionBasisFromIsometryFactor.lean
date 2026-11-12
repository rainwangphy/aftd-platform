import AFTD.Prelude
import AFTD.Kb.Tcs.PptQutritBellVector
import AFTD.Kb.Tcs.PptQutritSteeredNormalizer
import AFTD.Kb.Tcs.CslibSKIPolynomialEval

/-!
# ppt_qutrit_source_projection_basis_from_isometry_factor

Topic: quantum   Node: faf6e01b4e27

Provenance: helper lemma. Source-specific basis-selection helper for OP-693, using https://arxiv.org/abs/1405.4502.

Each rank-two qutrit projection has a plane basis whose first normalized-source contraction has full row rank, conditional only on factoring the projection into an isometry.
-/

open Matrix Polynomial
open scoped BigOperators Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
private lemma in767_basisproof_isometry_cols_independent (U : Matrix (Fin 3) (Fin 2) ℂ) (hU : Uᴴ*U=1) :
    LinearIndependent ℂ ![(fun i => U i 0),(fun i => U i 1)] := by
  have hinj : Function.Injective U.mulVec := by
    intro x y h
    have hh := congrArg (fun v => Uᴴ *ᵥ v) h
    simpa only [Matrix.mulVec_mulVec, hU, Matrix.one_mulVec] using hh
  have hcol := Matrix.mulVec_injective_iff.mp hinj
  have heq : ![(fun i => U i 0),(fun i => U i 1)] = U.col := by
    funext j i
    fin_cases j <;> rfl
  rw [heq]
  exact hcol

private lemma in767_basisproof_contraction_explicit (z : Fin 3 → ℂ) :
    (fun (a : Fin 3) (l : Fin 4) => ∑ b : Fin 3, ppt_qutrit_bell_vector l (a,b) * z b) =
    !![(Real.sqrt 2 : ℂ)⁻¹*z 0, ((Real.sqrt (131/2 : ℝ) : ℂ)/12)*z 1+z 2/60, ((Real.sqrt (131/2 : ℝ) : ℂ)/12)*z 0, -(Real.sqrt 3 : ℂ)⁻¹*z 1;
       (Real.sqrt 2 : ℂ)⁻¹*z 1, ((Real.sqrt (131/2 : ℝ) : ℂ)/12)*z 0, -((Real.sqrt (131/2 : ℝ) : ℂ)/12)*z 1+z 2/60, (Real.sqrt 3 : ℂ)⁻¹*z 0;
       0, -(3/10 : ℂ)*z 1, (3/10 : ℂ)*z 0, (Real.sqrt 3 : ℂ)⁻¹*z 2] := by
  ext i l
  fin_cases i <;> fin_cases l <;>
    simp [ppt_qutrit_bell_vector, Fin.sum_univ_three] <;> ring

private lemma in767_basisproof_contraction_minors (z : Fin 3 → ℂ) :
    let K : Matrix (Fin 3) (Fin 4) ℂ := fun a l => ∑ b : Fin 3, ppt_qutrit_bell_vector l (a,b) * z b
    let α : ℂ := ((Real.sqrt (131/2 : ℝ) : ℂ)/12)
    let q : ℂ := z 0 * (z 0*z 0 - 3*z 1*z 1)
    let p : ℂ := z 0*z 0*z 1 + ((10/3 : ℂ)*α)*z 0*z 0*z 2 + z 1*z 1*z 1 -
      ((10/3 : ℂ)*α)*z 1*z 1*z 2 - z 1*z 2*z 2/18
    (K.submatrix id ![0,1,2]).det = ((Real.sqrt 2 : ℂ)⁻¹)*α*(3/10)*q ∧
    (K.submatrix id ![0,1,3]).det = ((Real.sqrt 2 : ℂ)⁻¹)*((Real.sqrt 3 : ℂ)⁻¹)*(3/10)*p := by
  dsimp only
  rw [in767_basisproof_contraction_explicit]
  constructor <;> simp [Matrix.det_fin_three, Matrix.submatrix_apply] <;> ring



private lemma in767_basisproof_plane_yz_det_ne_zero
    (u v : Fin 3 → ℂ) (k : ℂ)
    (hu : u 0 = k*u 1) (hv : v 0 = k*v 1)
    (hli : LinearIndependent ℂ ![u,v]) : u 1 * v 2 - u 2 * v 1 ≠ 0 := by
  intro hd
  have hpair := LinearIndependent.pair_iff.mp hli
  have hz1 : (v 1) • u + (-u 1) • v = 0 := by
    ext i
    fin_cases i <;> simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    · change v 1 * u 0 + (-u 1) * v 0 = 0
      rw [hu, hv]; ring
    · change v 1 * u 1 + (-u 1) * v 1 = 0
      ring
    · change v 1 * u 2 + (-u 1) * v 2 = 0
      linear_combination -hd
  have hfirst := hpair (v 1) (-u 1) hz1
  have hv1 : v 1=0 := hfirst.1
  have hu1 : u 1=0 := by simpa using hfirst.2
  have hz2 : (v 2) • u + (-u 2) • v = 0 := by
    ext i
    fin_cases i <;> simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    · change v 2 * u 0 + (-u 2) * v 0 = 0
      rw [hu, hv, hu1, hv1]; ring
    · change v 2 * u 1 + (-u 2) * v 1 = 0
      rw [hu1, hv1]; ring
    · change v 2 * u 2 + (-u 2) * v 2 = 0
      ring
  have hsecond := hpair (v 2) (-u 2) hz2
  have hv2 : v 2=0 := hsecond.1
  have hu2 : u 2=0 := by simpa using hsecond.2
  have hz3 : (1 : ℂ) • u + (0 : ℂ) • v = 0 := by
    ext i
    fin_cases i <;> simp [hu, hu1, hu2]
  have := hpair 1 0 hz3
  norm_num at this

private lemma in767_basisproof_cubic_pair_no_common_plane
    (a : ℂ) (u v : Fin 3 → ℂ) (hli : LinearIndependent ℂ ![u, v]) :
    ∃ c d : ℂ,
      let x := c*u 0+d*v 0
      let y := c*u 1+d*v 1
      let z := c*u 2+d*v 2
      x*(x*x-3*y*y) ≠ 0 ∨
        x*x*y + a*x*x*z + y*y*y - a*y*y*z - y*z*z/18 ≠ 0 := by
  by_contra hcontra
  dsimp only at hcontra
  push_neg at hcontra
  let s : ℂ := Real.sqrt 3
  have hs : s*s=3 := by
    dsimp [s]
    have hh : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
    have hh' : (Real.sqrt 3 : ℂ)^2 = (3 : ℂ) := by exact_mod_cast hh
    simpa [pow_two] using hh'
  have hfact (x y : ℂ) : x*(x-s*y)*(x+s*y)=x*(x*x-3*y*y) := by
    linear_combination (-x*y*y) * hs
  let Xp : Polynomial ℂ := C (u 0) + X * C (v 0)
  let Yp : Polynomial ℂ := C (u 1) + X * C (v 1)
  have hpoly : Xp * (Xp - C s * Yp) * (Xp + C s * Yp) = 0 := by
    apply Polynomial.funext
    intro t
    have hq := (hcontra 1 t).1
    simp only [one_mul] at hq
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_add,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_zero, Xp, Yp]
    rw [hfact]
    exact hq
  have hlin : Xp = 0 ∨ Xp - C s * Yp = 0 ∨ Xp + C s * Yp = 0 := by
    rcases mul_eq_zero.mp hpoly with h | h
    · exact mul_eq_zero.mp h |>.imp_right Or.inl
    · exact Or.inr (Or.inr h)
  have hplane : ∃ k : ℂ, u 0 = k*u 1 ∧ v 0 = k*v 1 ∧ (k=0 ∨ k*k=3) := by
    rcases hlin with h | h | h
    · have h0 := congrArg (fun P : Polynomial ℂ => P.eval 0) h
      have h1 := congrArg (fun P : Polynomial ℂ => P.eval 1) h
      simp [Xp] at h0 h1
      refine ⟨0, by simpa using h0, ?_, Or.inl rfl⟩
      simpa [h0] using h1
    · have h0 := congrArg (fun P : Polynomial ℂ => P.eval 0) h
      have h1 := congrArg (fun P : Polynomial ℂ => P.eval 1) h
      simp [Xp, Yp] at h0 h1
      refine ⟨s, by linear_combination h0, ?_, Or.inr hs⟩
      linear_combination h1 - h0
    · have h0 := congrArg (fun P : Polynomial ℂ => P.eval 0) h
      have h1 := congrArg (fun P : Polynomial ℂ => P.eval 1) h
      simp [Xp, Yp] at h0 h1
      refine ⟨-s, by linear_combination h0, ?_, Or.inr ?_⟩
      · linear_combination h1 - h0
      · linear_combination hs
  obtain ⟨k, hu, hv, hk⟩ := hplane
  let D : ℂ := u 1*v 2-u 2*v 1
  have hD : D ≠ 0 := in767_basisproof_plane_yz_det_ne_zero u v k hu hv hli
  let c : ℂ := v 2 / D
  let d : ℂ := -u 2 / D
  have hy : c*u 1 + d*v 1 = 1 := by
    dsimp [c,d]
    field_simp [hD]
    dsimp [D]
    ring
  have hz : c*u 2 + d*v 2 = 0 := by
    dsimp [c,d]
    field_simp [hD]
    dsimp [D]
    ring
  have hx : c*u 0 + d*v 0 = k := by
    rw [hu,hv]
    linear_combination k*hy
  have hp := (hcontra c d).2
  rw [hx,hy,hz] at hp
  rcases hk with rfl | hk
  · norm_num at hp
  · have hh : (4 : ℂ) = 0 := by linear_combination hp - hk
    norm_num at hh


private def in767_basisproof_qpoly (z : Fin 3 → ℂ) : ℂ := z 0 * (z 0*z 0-3*z 1*z 1)
private noncomputable def in767_basisproof_ppoly (a : ℂ) (z : Fin 3 → ℂ) : ℂ :=
  z 0*z 0*z 1 + a*z 0*z 0*z 2 + z 1*z 1*z 1 - a*z 1*z 1*z 2 - z 1*z 2*z 2/18

private lemma in767_basisproof_cubics_four_real_directions
    (a : ℂ) (u v : Fin 3 → ℂ) (hli : LinearIndependent ℂ ![u,v]) :
    ∃ t : Fin 4,
      let r : Fin 4 → ℂ := ![0,1,-1,2]
      let z : Fin 3 → ℂ := fun i => u i+r t*v i
      in767_basisproof_qpoly z ≠ 0 ∨ in767_basisproof_ppoly a z ≠ 0 := by
  by_contra hcontra
  dsimp only at hcontra
  push_neg at hcontra
  have h0 := hcontra 0
  have h1 := hcontra 1
  have hm := hcontra 2
  have h2 := hcontra 3
  change in767_basisproof_qpoly (fun i => u i+0*v i)=0 ∧ in767_basisproof_ppoly a (fun i => u i+0*v i)=0 at h0
  change in767_basisproof_qpoly (fun i => u i+1*v i)=0 ∧ in767_basisproof_ppoly a (fun i => u i+1*v i)=0 at h1
  change in767_basisproof_qpoly (fun i => u i+(-1)*v i)=0 ∧ in767_basisproof_ppoly a (fun i => u i+(-1)*v i)=0 at hm
  change in767_basisproof_qpoly (fun i => u i+2*v i)=0 ∧ in767_basisproof_ppoly a (fun i => u i+2*v i)=0 at h2
  obtain ⟨c,d,h⟩ := in767_basisproof_cubic_pair_no_common_plane a u v hli
  dsimp only at h
  let L0 : ℂ := (c-d)*(c+d)*(2*c-d)/2
  let L1 : ℂ := d*(c+d)*(2*c-d)/2
  let Lm : ℂ := -d*(c-d)*(2*c-d)/6
  let L2 : ℂ := d*(d-c)*(d+c)/6
  have hq : (c*u 0+d*v 0)*((c*u 0+d*v 0)^2-3*(c*u 1+d*v 1)^2)=0 := by
    dsimp [in767_basisproof_qpoly] at h0 h1 hm h2
    linear_combination ((c-d)*(c+d)*(2*c-d)/2)*h0.1 + (d*(c+d)*(2*c-d)/2)*h1.1 + (-d*(c-d)*(2*c-d)/6)*hm.1 + (d*(d-c)*(d+c)/6)*h2.1
  have hp : (c*u 0+d*v 0)^2*(c*u 1+d*v 1) + a*(c*u 0+d*v 0)^2*(c*u 2+d*v 2) +
      (c*u 1+d*v 1)^3-a*(c*u 1+d*v 1)^2*(c*u 2+d*v 2) -
      (c*u 1+d*v 1)*(c*u 2+d*v 2)^2/18=0 := by
    dsimp [in767_basisproof_ppoly] at h0 h1 hm h2
    linear_combination ((c-d)*(c+d)*(2*c-d)/2)*h0.2 + (d*(c+d)*(2*c-d)/2)*h1.2 + (-d*(c-d)*(2*c-d)/6)*hm.2 + (d*(d-c)*(d+c)/6)*h2.2
  rcases h with h | h
  · apply h
    simpa [pow_two, mul_assoc] using hq
  · apply h
    simpa [pow_two, pow_succ, mul_assoc] using hp


private lemma in767_basisproof_source_rank_one_of_four_real_directions
    (U : Matrix (Fin 3) (Fin 2) ℂ)
    (hli : LinearIndependent ℂ ![(fun i => U i 0),(fun i => U i 1)]) :
    ∃ t : Fin 4,
      let r : Fin 4 → ℂ := ![0,1,-1,2]
      let x : Fin 2 → ℂ := ![1,r t]
      let z : Fin 3 → ℂ := U.mulVec x
      let K : Matrix (Fin 3) (Fin 4) ℂ := fun a l =>
        ∑ b : Fin 3, ppt_qutrit_bell_vector l (a,b) * z b
      K.rank = 3 := by
  let u : Fin 3 → ℂ := fun i => U i 0
  let v : Fin 3 → ℂ := fun i => U i 1
  let α : ℂ := (Real.sqrt (131/2 : ℝ) : ℂ)/12
  obtain ⟨t,h⟩ := in767_basisproof_cubics_four_real_directions ((10/3 : ℂ)*α) u v hli
  let r : Fin 4 → ℂ := ![0,1,-1,2]
  let x : Fin 2 → ℂ := ![1,r t]
  let z : Fin 3 → ℂ := U.mulVec x
  have hz (i : Fin 3) : z i = u i+r t*v i := by
    simp [z, x, u, v, Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_comm]
  dsimp only at h
  change (u 0+r t*v 0)*((u 0+r t*v 0)*(u 0+r t*v 0)-3*(u 1+r t*v 1)*(u 1+r t*v 1)) ≠ 0 ∨
    (u 0+r t*v 0)*(u 0+r t*v 0)*(u 1+r t*v 1)+((10/3 : ℂ)*α)*(u 0+r t*v 0)*(u 0+r t*v 0)*(u 2+r t*v 2)+
    (u 1+r t*v 1)*(u 1+r t*v 1)*(u 1+r t*v 1)-((10/3 : ℂ)*α)*(u 1+r t*v 1)*(u 1+r t*v 1)*(u 2+r t*v 2)-
    (u 1+r t*v 1)*(u 2+r t*v 2)*(u 2+r t*v 2)/18 ≠ 0 at h
  rw [← hz 0, ← hz 1, ← hz 2] at h
  let K : Matrix (Fin 3) (Fin 4) ℂ := fun a l => ∑ b : Fin 3, ppt_qutrit_bell_vector l (a,b) * z b
  have h2r : Real.sqrt (2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have h3r : Real.sqrt (3 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have har : Real.sqrt (131/2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast h2r
  have h3 : (Real.sqrt 3 : ℂ) ≠ 0 := by exact_mod_cast h3r
  have ha : α ≠ 0 := by dsimp [α]; exact div_ne_zero (by exact_mod_cast har) (by norm_num)
  have hminor := in767_basisproof_contraction_minors z
  change (K.submatrix id ![0,1,2]).det = _ ∧ (K.submatrix id ![0,1,3]).det = _ at hminor
  refine ⟨t, ?_⟩
  change K.rank = 3
  have hheight : K.rank ≤ 3 := by simpa using Matrix.rank_le_card_height K
  rcases h with hq | hp
  · have hdet : (K.submatrix id ![0,1,2]).det ≠ 0 := by
      rw [hminor.1]
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (inv_ne_zero h2) ha) (by norm_num)) hq
    have hfull : (K.submatrix id ![0,1,2]).rank = 3 := by
      simpa using Matrix.rank_of_det_ne_zero hdet
    have hle := Matrix.rank_submatrix_le K id ![0,1,2]
    omega
  · have hdet : (K.submatrix id ![0,1,3]).det ≠ 0 := by
      rw [hminor.2]
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (inv_ne_zero h2) (inv_ne_zero h3)) (by norm_num)) hp
    have hfull : (K.submatrix id ![0,1,3]).rank = 3 := by
      simpa using Matrix.rank_of_det_ne_zero hdet
    have hle := Matrix.rank_submatrix_le K id ![0,1,3]
    omega


private noncomputable def in767_basisproof_rotation (r : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((Real.sqrt (1+r*r))⁻¹ : ℝ) • !![1, -(r : ℂ); (r : ℂ), 1]

private lemma in767_basisproof_rotation_unitary (r : ℝ) :
    (in767_basisproof_rotation r)ᴴ * in767_basisproof_rotation r = 1 ∧
    in767_basisproof_rotation r * (in767_basisproof_rotation r)ᴴ = 1 := by
  have hpos : 0 < Real.sqrt (1+r*r) := Real.sqrt_pos.2 (by nlinarith [sq_nonneg r])
  have hne : Real.sqrt (1+r*r) ≠ 0 := ne_of_gt hpos
  have hsq : (Real.sqrt (1+r*r))^2=1+r*r := Real.sq_sqrt (by nlinarith [sq_nonneg r])
  simp only [← pow_two] at hsq hne hpos
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [in767_basisproof_rotation, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
      Complex.real_smul, Complex.mul_re, Complex.mul_im, hne] <;>
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> field_simp [hne] <;> nlinarith


private lemma in767_basisproof_normalizer_isUnit : IsUnit ppt_qutrit_steered_normalizer := by
  rw [ppt_qutrit_steered_normalizer, Matrix.isUnit_diagonal, Pi.isUnit_iff]
  intro i
  apply isUnit_iff_ne_zero.mpr
  split_ifs
  · exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 6884/10)))
  · exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 6884/3437)))


private lemma in767_basisproof_conjugate_composed_columns_independent
    (U : Matrix (Fin 3) (Fin 2) ℂ) (N : Matrix (Fin 3) (Fin 3) ℂ)
    (hU : Uᴴ*U=1) (hN : IsUnit N) :
    let J : Matrix (Fin 3) (Fin 2) ℂ := fun i j => star ((N*U) i j)
    LinearIndependent ℂ ![(fun i => J i 0),(fun i => J i 1)] := by
  let J : Matrix (Fin 3) (Fin 2) ℂ := fun i j => star ((N*U) i j)
  have hUi : Function.Injective U.mulVec := by
    intro x y h
    have hh := congrArg (fun v => Uᴴ *ᵥ v) h
    simpa only [Matrix.mulVec_mulVec, hU, Matrix.one_mulVec] using hh
  have hNi : Function.Injective N.mulVec := Matrix.mulVec_injective_of_isUnit hN
  have hQi : Function.Injective (N*U).mulVec := by
    intro x y h
    apply hUi
    apply hNi
    simpa only [Matrix.mulVec_mulVec] using h
  have hstar (x : Fin 2 → ℂ) : star (J*ᵥx) = (N*U)*ᵥ(star x) := by
    ext i
    simp [J, Matrix.mulVec, dotProduct, star_sum, star_mul, mul_comm]
  have hJi : Function.Injective J.mulVec := by
    intro x y h
    apply star_injective
    apply hQi
    simpa only [← hstar] using congrArg star h
  have hcol := Matrix.mulVec_injective_iff.mp hJi
  have heq : ![(fun i => J i 0),(fun i => J i 1)] = J.col := by
    funext j i
    fin_cases j <;> rfl
  change LinearIndependent ℂ ![(fun i => J i 0),(fun i => J i 1)]
  rw [heq]
  exact hcol

private lemma in767_basisproof_rotated_first_column (Q : Matrix (Fin 3) (Fin 2) ℂ) (r : ℝ) (i : Fin 3) :
    star ((Q * in767_basisproof_rotation r) i 0) =
      (((Real.sqrt (1+r*r))⁻¹ : ℝ) : ℂ) * (star (Q i 0) + (r : ℂ)*star (Q i 1)) := by
  simp [in767_basisproof_rotation, Matrix.mul_apply, Fin.sum_univ_two, Complex.real_smul, star_add, star_mul]
  ring

private lemma in767_basisproof_rotated_weighted_contraction_rank
    (Q : Matrix (Fin 3) (Fin 2) ℂ) (r : ℝ) (lam : Fin 4 → ℝ)
    (hlam : ∀ t, 0 < lam t)
    (hrank : (let J : Matrix (Fin 3) (Fin 2) ℂ := fun i j => star (Q i j)
      let z : Fin 3 → ℂ := J.mulVec ![1,(r : ℂ)]
      let K : Matrix (Fin 3) (Fin 4) ℂ := fun a l =>
        ∑ b : Fin 3, ppt_qutrit_bell_vector l (a,b) * z b
      K.rank=3)) :
    let W : Matrix (Fin 3) (Fin 2) ℂ := Q * in767_basisproof_rotation r
    let G : Matrix (Fin 3) (Fin 4) ℂ := fun i t =>
      (Real.sqrt (lam t) : ℂ) * (∑ x : Fin 3, star (W x 0) * ppt_qutrit_bell_vector t (i,x))
    G.rank=3 := by
  let J : Matrix (Fin 3) (Fin 2) ℂ := fun i j => star (Q i j)
  let z : Fin 3 → ℂ := J.mulVec ![1,(r : ℂ)]
  let K : Matrix (Fin 3) (Fin 4) ℂ := fun a l => ∑ b : Fin 3, ppt_qutrit_bell_vector l (a,b) * z b
  let δ : ℂ := (((Real.sqrt (1+r*r))⁻¹ : ℝ) : ℂ)
  let d : Fin 4 → ℂ := fun t => Real.sqrt (lam t)
  let W : Matrix (Fin 3) (Fin 2) ℂ := Q * in767_basisproof_rotation r
  let G : Matrix (Fin 3) (Fin 4) ℂ := fun i t =>
    (Real.sqrt (lam t) : ℂ) * (∑ x : Fin 3, star (W x 0) * ppt_qutrit_bell_vector t (i,x))
  have hsqrt : Real.sqrt (1+r*r) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by nlinarith [sq_nonneg r]))
  have hδ : δ ≠ 0 := by dsimp [δ]; exact_mod_cast inv_ne_zero hsqrt
  have hd : ∀ t, d t ≠ 0 := by
    intro t
    dsimp [d]
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (hlam t)))
  have hD : IsUnit (Matrix.diagonal d) := Matrix.isUnit_diagonal.mpr (Pi.isUnit_iff.mpr fun t => isUnit_iff_ne_zero.mpr (hd t))
  have hdet : IsUnit (Matrix.diagonal d).det := (Matrix.isUnit_iff_isUnit_det _).mp hD
  have hG : G = (δ • K) * Matrix.diagonal d := by
    ext i t
    simp only [Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul]
    dsimp only [G, W]
    simp_rw [in767_basisproof_rotated_first_column]
    simp [δ, K, z, J, d, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two,
      Finset.mul_sum]
    ring
  change G.rank = 3
  rw [hG, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hdet,
    Matrix.rank_smul_of_mem_nonZeroDivisors K (mem_nonZeroDivisors_of_ne_zero hδ)]
  exact hrank

theorem ppt_qutrit_source_projection_basis_from_isometry_factor
    (hfactor : ∀ P : Matrix (Fin 3) (Fin 3) ℂ, P.IsHermitian → P*P=P → P.rank=2 →
      ∃ U : Matrix (Fin 3) (Fin 2) ℂ, Uᴴ*U=1 ∧ U*Uᴴ=P) :
    ∀ P : Matrix (Fin 3) (Fin 3) ℂ, P.IsHermitian → P*P=P → P.rank=2 →
    ∃ U : Matrix (Fin 3) (Fin 2) ℂ,
      Uᴴ*U=1 ∧ U*Uᴴ=P ∧
      (let W : Matrix (Fin 3) (Fin 2) ℂ := ppt_qutrit_steered_normalizer * U
       let lam : Fin 4 → ℝ := fun t => if t = 0 then 3257/6884 else if t = 3 then 27/6884 else 450/1721
       let G : Matrix (Fin 3) (Fin 4) ℂ := fun i t =>
        (Real.sqrt (lam t) : ℂ) * (∑ x : Fin 3, star (W x 0) * ppt_qutrit_bell_vector t (i,x))
       G.rank=3) := by
  intro P hP hPP hRank
  obtain ⟨U0, hU0, hU0P⟩ := hfactor P hP hPP hRank
  let N := ppt_qutrit_steered_normalizer
  let Q : Matrix (Fin 3) (Fin 2) ℂ := N*U0
  let J : Matrix (Fin 3) (Fin 2) ℂ := fun i j => star (Q i j)
  have hli : LinearIndependent ℂ ![(fun i => J i 0),(fun i => J i 1)] :=
    in767_basisproof_conjugate_composed_columns_independent U0 N hU0 in767_basisproof_normalizer_isUnit
  obtain ⟨t, ht⟩ := in767_basisproof_source_rank_one_of_four_real_directions J hli
  let rr : Fin 4 → ℝ := ![0,1,-1,2]
  let rc : Fin 4 → ℂ := ![0,1,-1,2]
  let r : ℝ := rr t
  have hrc : (r : ℂ) = rc t := by
    fin_cases t <;> norm_num [r, rr, rc]
  have hKr : (let z : Fin 3 → ℂ := J.mulVec ![1,(r : ℂ)]
      let K : Matrix (Fin 3) (Fin 4) ℂ := fun a l =>
        ∑ b : Fin 3, ppt_qutrit_bell_vector l (a,b) * z b
      K.rank=3) := by
    rw [hrc]
    exact ht
  let R : Matrix (Fin 2) (Fin 2) ℂ := in767_basisproof_rotation r
  let U : Matrix (Fin 3) (Fin 2) ℂ := U0*R
  have hR := in767_basisproof_rotation_unitary r
  have hU : Uᴴ*U=1 := by
    change (U0*R)ᴴ*(U0*R)=1
    calc
      (U0*R)ᴴ*(U0*R) = Rᴴ*(U0ᴴ*U0)*R := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hU0]; simpa [R] using hR.1
  have hUP : U*Uᴴ=P := by
    change (U0*R)*(U0*R)ᴴ=P
    calc
      (U0*R)*(U0*R)ᴴ = U0*(R*Rᴴ)*U0ᴴ := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = P := by rw [show R*Rᴴ=1 from hR.2]; simpa using hU0P
  let lam : Fin 4 → ℝ := fun t => if t = 0 then 3257/6884 else if t = 3 then 27/6884 else 450/1721
  have hlam : ∀ t, 0 < lam t := by intro t; dsimp [lam]; split_ifs <;> norm_num
  have hG := in767_basisproof_rotated_weighted_contraction_rank Q r lam hlam hKr
  refine ⟨U, hU, hUP, ?_⟩
  change (let W : Matrix (Fin 3) (Fin 2) ℂ := N*(U0*R)
    let G : Matrix (Fin 3) (Fin 4) ℂ := fun i t =>
      (Real.sqrt (lam t) : ℂ) * (∑ x : Fin 3, star (W x 0) * ppt_qutrit_bell_vector t (i,x))
    G.rank=3)
  rw [← Matrix.mul_assoc N U0 R]
  exact hG
