import AFTD.Prelude
import AFTD.Kb.Tcs.PrimeConvolutionCriticalEnv
import AFTD.Kb.Tcs.PrimeConvolutionTwoSupportOrbitFormula
import AFTD.Kb.Tcs.TwoLevelPsi

/-!
# prime_convolution_critical_env_orbit_decomposition

Topic: quantum   Node: 20395974aeed

Provenance: helper lemma. OP-2466 product-orbit decomposition

The critical two-level environment is one two-support product orbit plus a nonnegative diagonal matrix for every allowed prime dimension and coupling.
-/

open Fin.CommRing
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

theorem in1249_prime_fin_nonzero (n : ℕ) (hp : (n+2).Prime) (h5 : 5 ≤ n+2)
    (r : Fin (n+2)) (hr1 : r ≠ 1) :
    (2 : Fin (n+2)) ≠ 0 ∧ 2*(1-r) ≠ 0 := by
  letI : Fact (Nat.Prime (n+2)) := ⟨hp⟩
  let e := ZMod.finEquiv (n+2)
  have hz2 : (2 : ZMod (n+2)) ≠ 0 := by
    intro h
    have hdvd : n+2 ∣ 2 := (ZMod.natCast_eq_zero_iff 2 (n+2)).mp h
    have hlt : 0 < 2 ∧ 2 < n+2 := by omega
    exact (Nat.not_dvd_of_pos_of_lt hlt.1 hlt.2) hdvd
  have he2 : e 2 = (2 : ZMod (n+2)) := by
    calc e 2 = e (1 + 1) := by congr 1 <;> norm_num
         _ = e 1 + e 1 := map_add e 1 1
         _ = 2 := by simp only [map_one]; exact one_add_one_eq_two
  have he1 : e (1-r) = 1 - e r := by simp [e]
  have hfr : 1-e r ≠ 0 := by
    intro h
    have heq : e r = e 1 := by simpa using (sub_eq_zero.mp h).symm
    exact hr1 (e.injective heq)
  constructor
  · intro h
    have := congrArg e h
    simp [he2] at this
    exact hz2 this
  · intro h
    have hz : (2 : ZMod (n+2)) * (1-e r) = 0 := by
      have := congrArg e h
      simpa [he2,he1] using this
    exact (mul_ne_zero hz2 hfr) hz


open Fin.CommRing

open Fin.CommRing in
theorem prime_convolution_critical_env_orbit_decomposition
    (n : ℕ) (hp : (n+2).Prime) (h5 : 5 ≤ n+2)
    (r : Fin (n+2)) (hr0 : r ≠ 0) (hr1 : r ≠ 1) (hr2 : 2*r ≠ 1)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∃ (a b w : Fin (n+2) → ℝ), (∀ j, 0 ≤ w j) ∧
      prime_convolution_critical_env (n+2) p =
        (Matrix.of fun j l =>
          ((∑ i, a i * b (r*i+j) * a (i+j-l) * b (r*(i+j-l)+l) : ℝ) : ℂ)) +
        Matrix.diagonal (fun j => (w j : ℂ)) := by
  classical
  let A := Real.sqrt (Real.sqrt p)
  let B := Real.sqrt (Real.sqrt (1-p))
  let q := Real.sqrt (p*(1-p))
  let a := in1249_A n A B
  let b := in1249_B n r A B
  let w : Fin (n+2) → ℝ := fun j => if j=r ∨ j=1-r then 0 else q
  refine ⟨a,b,w, ?_, ?_⟩
  · intro j
    dsimp [w, q]
    split_ifs <;> positivity
  · have hp1' : 0 ≤ 1-p := by linarith
    have ha : A^2 = Real.sqrt p := Real.sq_sqrt (Real.sqrt_nonneg p)
    have hb : B^2 = Real.sqrt (1-p) := Real.sq_sqrt (Real.sqrt_nonneg (1-p))
    have hq : A^2*B^2 = q := by
      rw [ha,hb]
      dsimp [q]
      rw [Real.sqrt_mul hp0]
    obtain ⟨htwo,hdouble⟩ := in1249_prime_fin_nonzero n hp h5 r hr1
    have hpsi (j : Fin (n+2)) : in1249_P n A B j = two_level_psi (n+2) p j := by
      have h0 : ((j : ℕ) = 0) ↔ j=0 := by
        constructor
        · intro h; apply Fin.ext; simpa using h
        · intro h; subst j; rfl
      have h1 : ((j : ℕ) = 1) ↔ j=1 := by
        constructor
        · intro h; apply Fin.ext; simpa using h
        · intro h; subst j; simp
      simp [in1249_P, two_level_psi, h0,h1,ha,hb]
    ext j l
    rw [Matrix.add_apply, Matrix.of_apply, Matrix.diagonal_apply]
    have ho := prime_convolution_two_support_orbit_formula n r hr0 hr1 hr2 htwo hdouble A B j l
    change _ = ((∑ i, in1249_A n A B i * in1249_B n r A B (r*i+j) *
      in1249_A n A B (i+j-l) * in1249_B n r A B (r*(i+j-l)+l) : ℝ) : ℂ) + _
    rw [ho, hpsi j, hpsi l, hq]
    simp only [prime_convolution_critical_env, Matrix.add_apply, Matrix.of_apply, Matrix.smul_apply,
      smul_eq_mul, Matrix.one_apply]
    dsimp [w]
    by_cases hjl : j=l
    · subst l
      by_cases hj : j=r ∨ j=1-r
      · simp [hj, q]
      · simp [hj, q]
    · simp [hjl]
