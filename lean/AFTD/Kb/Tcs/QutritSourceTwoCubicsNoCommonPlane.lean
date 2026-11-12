import AFTD.Prelude
import AFTD.Kb.Tcs.CslibSKIPolynomialEval

/-!
# qutrit_source_two_cubics_no_common_plane

Topic: quantum   Node: 0ab3f757f0a6

Provenance: helper lemma. Helper for OP-693, using the rank-four PPT source from https://arxiv.org/abs/1405.4502 and the normal-completion context https://arxiv.org/abs/0903.0090.

Two explicit cubic maximal minors of the source vectors cannot both vanish on a complex two-dimensional plane.
-/

open Matrix Polynomial
open scoped BigOperators Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
private lemma in767_cubicproof_plane_yz_det_ne_zero
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

private lemma in767_cubicproof_cubic_pair_no_common_plane
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
  have hD : D ≠ 0 := in767_cubicproof_plane_yz_det_ne_zero u v k hu hv hli
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

theorem qutrit_source_two_cubics_no_common_plane :
  ∀ (a : ℂ) (u v : Fin 3 → ℂ), LinearIndependent ℂ ![u, v] →
    ∃ c d : ℂ,
      let x := c*u 0+d*v 0
      let y := c*u 1+d*v 1
      let z := c*u 2+d*v 2
      x*(x*x-3*y*y) ≠ 0 ∨
        x*x*y + a*x*x*z + y*y*y - a*y*y*z - y*z*z/18 ≠ 0 := by
  intro a u v hli
  exact in767_cubicproof_cubic_pair_no_common_plane a u v hli
