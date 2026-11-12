import AFTD.Prelude
import AFTD.Kb.Tcs.PptQutritBellVector
import AFTD.Kb.Tcs.QutritSourceTwoCubicsNoCommonPlane
import AFTD.Kb.Tcs.CslibSKIPolynomialEval

/-!
# ppt_qutrit_bell_source_full_rank_on_every_plane

Topic: quantum   Node: 3aeee8f5166c

Provenance: helper lemma. Source-specific rank helper for OP-693, using https://arxiv.org/abs/1405.4502.

The contraction of the four source vectors has full qutrit row rank for some vector in each complex two-plane.
-/

open Matrix Polynomial
open scoped BigOperators Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
private lemma in767_rankproof_isometry_cols_independent (U : Matrix (Fin 3) (Fin 2) ℂ) (hU : Uᴴ*U=1) :
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

private lemma in767_rankproof_contraction_explicit (z : Fin 3 → ℂ) :
    (fun (a : Fin 3) (l : Fin 4) => ∑ b : Fin 3, ppt_qutrit_bell_vector l (a,b) * z b) =
    !![(Real.sqrt 2 : ℂ)⁻¹*z 0, ((Real.sqrt (131/2 : ℝ) : ℂ)/12)*z 1+z 2/60, ((Real.sqrt (131/2 : ℝ) : ℂ)/12)*z 0, -(Real.sqrt 3 : ℂ)⁻¹*z 1;
       (Real.sqrt 2 : ℂ)⁻¹*z 1, ((Real.sqrt (131/2 : ℝ) : ℂ)/12)*z 0, -((Real.sqrt (131/2 : ℝ) : ℂ)/12)*z 1+z 2/60, (Real.sqrt 3 : ℂ)⁻¹*z 0;
       0, -(3/10 : ℂ)*z 1, (3/10 : ℂ)*z 0, (Real.sqrt 3 : ℂ)⁻¹*z 2] := by
  ext i l
  fin_cases i <;> fin_cases l <;>
    simp [ppt_qutrit_bell_vector, Fin.sum_univ_three] <;> ring

private lemma in767_rankproof_contraction_minors (z : Fin 3 → ℂ) :
    let K : Matrix (Fin 3) (Fin 4) ℂ := fun a l => ∑ b : Fin 3, ppt_qutrit_bell_vector l (a,b) * z b
    let α : ℂ := ((Real.sqrt (131/2 : ℝ) : ℂ)/12)
    let q : ℂ := z 0 * (z 0*z 0 - 3*z 1*z 1)
    let p : ℂ := z 0*z 0*z 1 + ((10/3 : ℂ)*α)*z 0*z 0*z 2 + z 1*z 1*z 1 -
      ((10/3 : ℂ)*α)*z 1*z 1*z 2 - z 1*z 2*z 2/18
    (K.submatrix id ![0,1,2]).det = ((Real.sqrt 2 : ℂ)⁻¹)*α*(3/10)*q ∧
    (K.submatrix id ![0,1,3]).det = ((Real.sqrt 2 : ℂ)⁻¹)*((Real.sqrt 3 : ℂ)⁻¹)*(3/10)*p := by
  dsimp only
  rw [in767_rankproof_contraction_explicit]
  constructor <;> simp [Matrix.det_fin_three, Matrix.submatrix_apply] <;> ring


private lemma in767_rankproof_plane_yz_det_ne_zero
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

private lemma in767_rankproof_cubic_pair_no_common_plane
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
  have hD : D ≠ 0 := in767_rankproof_plane_yz_det_ne_zero u v k hu hv hli
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


private lemma in767_rankproof_source_full_rank_on_plane (U : Matrix (Fin 3) (Fin 2) ℂ) (hU : Uᴴ*U=1) :
    ∃ x : Fin 2 → ℂ,
      let z : Fin 3 → ℂ := U.mulVec x
      let K : Matrix (Fin 3) (Fin 4) ℂ := fun a l =>
        ∑ b : Fin 3, ppt_qutrit_bell_vector l (a,b) * z b
      K.rank = 3 := by
  let u : Fin 3 → ℂ := fun i => U i 0
  let v : Fin 3 → ℂ := fun i => U i 1
  let α : ℂ := (Real.sqrt (131/2 : ℝ) : ℂ)/12
  have hli : LinearIndependent ℂ ![u,v] := in767_rankproof_isometry_cols_independent U hU
  obtain ⟨c,d,h⟩ := in767_rankproof_cubic_pair_no_common_plane ((10/3 : ℂ)*α) u v hli
  let x : Fin 2 → ℂ := ![c,d]
  let z : Fin 3 → ℂ := U.mulVec x
  have hz (i : Fin 3) : z i = c*u i+d*v i := by
    simp [z, x, u, v, Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_comm]
  dsimp only at h
  rw [← hz 0, ← hz 1, ← hz 2] at h
  let K : Matrix (Fin 3) (Fin 4) ℂ := fun a l => ∑ b : Fin 3, ppt_qutrit_bell_vector l (a,b) * z b
  have h2r : Real.sqrt (2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have h3r : Real.sqrt (3 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have har : Real.sqrt (131/2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast h2r
  have h3 : (Real.sqrt 3 : ℂ) ≠ 0 := by exact_mod_cast h3r
  have ha : α ≠ 0 := by dsimp [α]; exact div_ne_zero (by exact_mod_cast har) (by norm_num)
  have hminor := in767_rankproof_contraction_minors z
  change (K.submatrix id ![0,1,2]).det = _ ∧ (K.submatrix id ![0,1,3]).det = _ at hminor
  refine ⟨x, ?_⟩
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

theorem ppt_qutrit_bell_source_full_rank_on_every_plane :
  ∀ U : Matrix (Fin 3) (Fin 2) ℂ, Uᴴ * U = 1 →
    ∃ x : Fin 2 → ℂ,
      let z : Fin 3 → ℂ := U.mulVec x
      let K : Matrix (Fin 3) (Fin 4) ℂ := fun a l =>
        ∑ b : Fin 3, ppt_qutrit_bell_vector l (a,b) * z b
      K.rank = 3 := by
  intro U hU
  exact in767_rankproof_source_full_rank_on_plane U hU
