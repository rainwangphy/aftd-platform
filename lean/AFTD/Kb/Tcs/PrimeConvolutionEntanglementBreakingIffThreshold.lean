import AFTD.Prelude
import AFTD.Kb.Tcs.PrimeConvolutionChoi
import AFTD.Kb.Tcs.TwoLevelEnvironment
import AFTD.Kb.Tcs.MatrixIsSeparable
import AFTD.Kb.Tcs.TwoLevelPsi
import AFTD.Kb.Tcs.PrimeConvolutionCriticalEnv
import AFTD.Kb.Tcs.PrimeConvolutionFiveTwoFifthEntanglementBreakingIff
import AFTD.Kb.Tcs.PrimeConvolutionSeparableImpThreshold
import AFTD.Kb.Tcs.Support

/-!
# prime_convolution_entanglement_breaking_iff_threshold

Topic: quantum   Node: 709f9695e7cb

Provenance: original. Related work: OP-2466 (proposed here; it builds on the qutrit convolution channels of arXiv:2609.16200, whose Theorem 8 gives the exact PPT and entanglement-breaking threshold 2/5 on a balanced two-level qutrit slice, and on arXiv:2611.09594, which shows PPT and entanglement breaking differ for another convolution environment). The entry asks whether the channel is entanglement breaking exactly up to the PPT boundary; the stabilizer-mixture theorem gives only a sufficient condition.

Let d be a prime with d ≥ 5, r ∈ ZMod d with r ≠ 0, r ≠ 1 and 2r ≠ 1 (r is not the inverse of 2), and p, t real numbers in [0, 1]. The normalised Choi matrix prime_convolution_choi d r (two_level_environment d p t) of the channel N_{r,p,t}(ρ) = Tr_2[U_r(ρ ⊗ σ_{p,t})U_r†] is separable (matrix_is_separable d d), i.e. the channel is entanglement breaking, if and only if t ≤ 1/(1 + d·√(p(1 − p))).
-/

open Fin.CommRing
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.all false

variable {F : Type*} [CommRing F] [Nontrivial F] [DecidableEq F]

def in1249full_rectP (A B : ℝ) (j : F) : ℝ :=
  if j=0 then A^2 else if j=1 then B^2 else 0

def in1249full_rectB (r : F) (A B : ℝ) (j : F) : ℝ :=
  if j=0 then A else if j=1-r then B else 0

-- Case j=l: the four distinct offsets are 0, 1, r, 1-r.
theorem in1249full_rect_twirl_diagonal (r : F) (hr0 : r ≠ 0) (hr1 : r ≠ 1)
    (hr2 : 2*r ≠ 1) (A B : ℝ) (j : F) :
    A^2 * in1249full_rectB r A B j ^2 + B^2 * in1249full_rectB r A B (j-r)^2 =
      in1249full_rectP A B j ^2 + A^2*B^2 * (if j=r ∨ j=1-r then 1 else 0) := by
  have hr1r : r ≠ 1-r := by intro h; apply hr2; linear_combination h
  have hr10 : 1-r ≠ 0 := by intro h; apply hr1; linear_combination -h
  have hr11 : 1-r ≠ 1 := by intro h; apply hr0; linear_combination -h
  have e0 : j-r=0 ↔ j=r := sub_eq_zero
  have e1 : j-r=1-r ↔ j=1 := by constructor <;> intro h <;> linear_combination h
  simp only [in1249full_rectB, in1249full_rectP, e0, e1]
  by_cases h0 : j=0
  · subst j; simp [hr0, hr1, hr2, hr10, hr11, hr1r, Ne.symm hr0, Ne.symm hr10] <;> ring
  · by_cases h1 : j=1
    · subst j; simp [hr0, hr1, hr2, hr10, hr11, hr1r, Ne.symm hr1, Ne.symm hr11] <;> ring
    · by_cases h2 : j=r
      · subst j; simp [h0,h1,hr0,hr1,hr1r,hr10,hr11] <;> ring
      · by_cases h3 : j=1-r
        · subst j; simp [h0,h1,h2,hr0,hr1,hr1r,hr10,hr11, Ne.symm hr1r]
        · simp [h0,h1,h2,h3]

-- The only overlapping translates of the two-support orbit occur at j=0.
theorem in1249full_rect_B_overlap (r : F) (hr1 : r ≠ 1) (hdouble : 2*(1-r) ≠ 0)
    (A B : ℝ) (j : F) :
    in1249full_rectB r A B j * in1249full_rectB r A B (j+1-r) = if j=0 then A*B else 0 := by
  have hr10 : 1-r ≠ 0 := by intro h; apply hr1; linear_combination -h
  have ht0 : (1-r)+(1-r) ≠ 0 := by
    intro h
    apply hdouble
    linear_combination h
  have hts : (1-r)+(1-r) ≠ 1-r := by
    intro h; apply hr10; linear_combination h
  by_cases h0 : j=0
  · subst j
    simp [in1249full_rectB, hr10]
  · by_cases h1 : j=1-r
    · subst j
      have heq : (1-r)+1-r = (1-r)+(1-r) := by ring
      rw [heq]
      simp [in1249full_rectB, hr10, ht0, hts]
    · simp [in1249full_rectB, h0, h1]

theorem in1249full_rect_P_overlap (htwo : (2 : F) ≠ 0) (A B : ℝ) (j : F) :
    in1249full_rectP A B j * in1249full_rectP A B (j+1) = if j=0 then A^2*B^2 else 0 := by
  by_cases h0 : j=0
  · subst j
    simp [in1249full_rectP]
  · by_cases h1 : j=1
    · subst j
      have h21 : (1 : F)+1 ≠ 1 := by
        intro h
        have hh : (1 : F)=0 := by linear_combination h
        exact one_ne_zero hh
      have h20 : (1 : F)+1 ≠ 0 := by intro h; apply htwo; linear_combination h
      simp [in1249full_rectP, h20, h21]
    · simp [in1249full_rectP, h0, h1]

def in1249full_rectA (A B : ℝ) (j : F) : ℝ :=
  if j=0 then A else if j= -1 then B else 0

theorem in1249full_rect_twirl_algebra (r : F) (hr0 : r ≠ 0) (hr1 : r ≠ 1)
    (hr2 : 2*r ≠ 1) (htwo : (2 : F) ≠ 0) (hdouble : 2*(1-r) ≠ 0) (A B : ℝ) (j l : F) :
    A * in1249full_rectB r A B j * in1249full_rectA A B (j-l) * in1249full_rectB r A B (r*(j-l)+l) +
    B * in1249full_rectB r A B (j-r) * in1249full_rectA A B (j-l-1) * in1249full_rectB r A B (r*(j-l-1)+l) =
      in1249full_rectP A B j * in1249full_rectP A B l +
        A^2*B^2 * (if j=l ∧ (j=r ∨ j=1-r) then 1 else 0) := by
  have hneg : (-1 : F) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have htwo' : (1 : F) ≠ -1 := by intro h; apply htwo; linear_combination h
  have hm2 : (-1 : F) - 1 ≠ 0 := by intro h; apply htwo; linear_combination -h
  have hm21 : (-1 : F) - 1 ≠ -1 := by
    intro h
    have hh : (1 : F) = 0 := by linear_combination -h
    exact one_ne_zero hh
  by_cases h0 : j=l
  · subst l
    simp only [sub_self, mul_zero, zero_add, zero_sub, in1249full_rectA, if_pos rfl, hneg, if_false, true_and]
    simp only [if_true]
    have he : r * (-1) + j = j-r := by ring
    rw [he]
    have hd := in1249full_rect_twirl_diagonal r hr0 hr1 hr2 A B j
    nlinarith [hd]
  · by_cases hp : j-l=1
    · have hj : j=l+1 := by linear_combination hp
      subst j
      have hl : l+1 ≠ l := by
        intro h
        have hh : (1 : F) = 0 := by linear_combination h
        exact one_ne_zero hh
      simp only [add_sub_cancel_left, in1249full_rectA, one_ne_zero, htwo', if_false, sub_self, if_pos rfl,
        mul_zero, zero_add, hl, false_and, ↓reduceIte, mul_zero, add_zero]
      have hb := in1249full_rect_B_overlap r hr1 hdouble A B l
      have hc := in1249full_rect_P_overlap htwo A B l
      by_cases hz : l = 0
      · simp only [if_pos hz] at hb hc
        linear_combination (A*B)*hb - hc
      · simp only [if_neg hz] at hb hc
        linear_combination (A*B)*hb - hc
    · by_cases hm : j-l= -1
      · have hl : l=j+1 := by linear_combination -hm
        subst l
        have hj : j ≠ j+1 := by
          intro h
          have hh : (1 : F) = 0 := by linear_combination -h
          exact one_ne_zero hh
        have he : j-(j+1) = (-1 : F) := by ring
        rw [he]
        simp only [in1249full_rectA, hneg, if_false, if_pos rfl,
          hm2, hm21, mul_zero, zero_add, hj, false_and, ↓reduceIte, add_zero]
        have hb := in1249full_rect_B_overlap r hr1 hdouble A B j
        have hc := in1249full_rect_P_overlap htwo A B j
        have hzarg : r*(-1)+(j+1) = j+1-r := by ring
        rw [hzarg]
        by_cases hz : j = 0
        · simp only [if_pos hz] at hb hc
          linear_combination (A*B)*hb - hc
        · simp only [if_neg hz] at hb hc
          linear_combination (A*B)*hb - hc
      · have hsub0 : j-l ≠ 0 := sub_ne_zero.mpr h0
        have hsub10 : j-l-1 ≠ 0 := by intro h; apply hp; linear_combination h
        have hsub1n : j-l-1 ≠ -1 := by intro h; apply hsub0; linear_combination h
        have hP : in1249full_rectP A B j * in1249full_rectP A B l = 0 := by
          simp only [in1249full_rectP]
          split_ifs with a b c d <;> simp_all <;> try ring
          all_goals exfalso <;> first | apply hp | apply hm | apply h0 <;> linear_combination a + b
        simp [in1249full_rectA, hsub0, hm, hsub10, hsub1n, h0, hP]

open Fin.CommRing
def in1249full_A (n : ℕ) (A B : ℝ) (i : Fin (n+2)) : ℝ :=
  if i = 0 then A else if i = -1 then B else 0

def in1249full_B (n : ℕ) (r : Fin (n+2)) (A B : ℝ) (i : Fin (n+2)) : ℝ :=
  if i = 0 then A else if i = 1-r then B else 0

def in1249full_P (n : ℕ) (A B : ℝ) (i : Fin (n+2)) : ℝ :=
  if i = 0 then A^2 else if i = 1 then B^2 else 0

theorem in1249full_twirl_support (n : ℕ) (r : Fin (n+2)) (A B : ℝ)
    (j l : Fin (n+2)) :
    (∑ i, in1249full_A n A B i * in1249full_B n r A B (r*i+j) *
      in1249full_A n A B (i+j-l) * in1249full_B n r A B (r*(i+j-l)+l)) =
    A * in1249full_B n r A B j * in1249full_A n A B (j-l) * in1249full_B n r A B (r*(j-l)+l) +
    B * in1249full_B n r A B (j-r) * in1249full_A n A B (j-l-1) * in1249full_B n r A B (r*(j-l-1)+l) := by
  have h01 : (0 : Fin (n+2)) ≠ -1 := by
    intro h
    have h1 : (1 : Fin (n+2)) = 0 := by linear_combination h
    have h1v : ((1 : Fin (n+2)) : ℕ) = 1 := by simp
    rw [h1] at h1v
    simp at h1v
  rw [Fintype.sum_eq_add 0 (-1) h01]
  · have h10 : (-1 : Fin (n+2)) ≠ 0 := Ne.symm h01
    simp only [in1249full_A, if_pos rfl, h01, h10, if_false, if_true]
    congr 1 <;> congr 1 <;> congr 1 <;> try ring
  · intro i ⟨hi0, hi1⟩
    simp [in1249full_A, hi0, hi1]


theorem in1249full_twirl_complete (n : ℕ) (r : Fin (n+2))
    (hr0 : r ≠ 0) (hr1 : r ≠ 1) (hr2 : 2*r ≠ 1)
    (htwo : (2 : Fin (n+2)) ≠ 0) (hdouble : 2*(1-r) ≠ 0)
    (A B : ℝ) (j l : Fin (n+2)) :
    (∑ i, in1249full_A n A B i * in1249full_B n r A B (r*i+j) *
      in1249full_A n A B (i+j-l) * in1249full_B n r A B (r*(i+j-l)+l)) =
      in1249full_P n A B j * in1249full_P n A B l +
        A^2*B^2 * (if j=l ∧ (j=r ∨ j=1-r) then 1 else 0) := by
  rw [in1249full_twirl_support]
  exact in1249full_rect_twirl_algebra r hr0 hr1 hr2 htwo hdouble A B j l

def in1249full_basis (n : ℕ) (k : Fin (n+2)) (j : Fin (n+2)) : ℝ := if j=k then 1 else 0

theorem in1249full_basis_orbit (n : ℕ) (r k j l : Fin (n+2)) :
    (∑ i, in1249full_basis n 0 i * in1249full_basis n k (r*i+j) *
      in1249full_basis n 0 (i+j-l) * in1249full_basis n k (r*(i+j-l)+l)) =
      in1249full_basis n k j * in1249full_basis n k l := by
  classical
  rw [Finset.sum_eq_single 0]
  · simp only [in1249full_basis, if_pos rfl, zero_mul, zero_add, one_mul]
    by_cases h : j = l
    · subst l
      simp [in1249full_basis]
    · have hsub : j-l ≠ 0 := sub_ne_zero.mpr h
      simp [in1249full_basis, h, hsub]; aesop
  · intro i _ hi
    simp [in1249full_basis, hi]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem in1249full_basis_choi_sep (n : ℕ) (r k : Fin (n+2)) :
    matrix_is_separable (n+2) (n+2)
      (prime_convolution_choi (n+2) r (Matrix.of fun j l => (in1249full_basis n k j * in1249full_basis n k l : ℂ))) := by
  have h := in1243_twirl_sep n r (in1249full_basis n 0) (in1249full_basis n k)
  convert h using 1
  congr 1
  ext j l
  simp only [Matrix.of_apply, ← Complex.ofReal_mul]
  exact congrArg (fun x : ℝ => (x : ℂ)) (in1249full_basis_orbit n r k j l).symm

theorem in1249full_diag_choi_sep (n : ℕ) (r : Fin (n+2)) (w : Fin (n+2) → ℝ)
    (hw : ∀ j, 0 ≤ w j) :
    matrix_is_separable (n+2) (n+2)
      (prime_convolution_choi (n+2) r (Matrix.diagonal (fun j => (w j : ℂ)))) := by
  classical
  let D : Fin (n+2) → Matrix (Fin (n+2)) (Fin (n+2)) ℂ :=
    fun k => Matrix.of fun j l => (in1249full_basis n k j * in1249full_basis n k l : ℂ)
  have heq : Matrix.diagonal (fun j => (w j : ℂ)) = ∑ k ∈ Finset.univ, (w k : ℂ) • D k := by
    ext j l
    simp only [Matrix.diagonal_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, D, Matrix.of_apply,
      in1249full_basis]
    by_cases h : j = l
    · subst l
      rw [Finset.sum_eq_single j]
      · simp
      · intro k _ hj
        have : j ≠ k := Ne.symm hj
        simp [this]
      · simp
    · simp only [apply_ite (fun a : ℝ => (a : ℂ)), Complex.ofReal_one, Complex.ofReal_zero]
      rw [Finset.sum_eq_zero]
      · simp [h]
      · intro k _
        by_cases hj : j=k <;> by_cases hl : l=k <;> simp_all
  rw [heq, in1243_choi_linear (n+2) (r : ZMod (n+2)) Finset.univ w D]
  apply in1243_sep_sum
  intro k _
  exact in1243_sep_smul _ _ _ (hw k) _ (in1249full_basis_choi_sep n r k)

theorem in1249full_prime_fin_nonzero (n : ℕ) (hp : (n+2).Prime) (h5 : 5 ≤ n+2)
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

theorem in1249full_critical_orbit_decomposition
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
  let a := in1249full_A n A B
  let b := in1249full_B n r A B
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
    obtain ⟨htwo,hdouble⟩ := in1249full_prime_fin_nonzero n hp h5 r hr1
    have hpsi (j : Fin (n+2)) : in1249full_P n A B j = two_level_psi (n+2) p j := by
      have h0 : ((j : ℕ) = 0) ↔ j=0 := by
        constructor
        · intro h; apply Fin.ext; simpa using h
        · intro h; subst j; rfl
      have h1 : ((j : ℕ) = 1) ↔ j=1 := by
        constructor
        · intro h; apply Fin.ext; simpa using h
        · intro h; subst j; simp
      simp [in1249full_P, two_level_psi, h0,h1,ha,hb]
    ext j l
    rw [Matrix.add_apply, Matrix.of_apply, Matrix.diagonal_apply]
    have ho := in1249full_twirl_complete n r hr0 hr1 hr2 htwo hdouble A B j l
    change _ = ((∑ i, in1249full_A n A B i * in1249full_B n r A B (r*i+j) *
      in1249full_A n A B (i+j-l) * in1249full_B n r A B (r*(i+j-l)+l) : ℝ) : ℂ) + _
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

theorem in1249full_choi_add (d : ℕ) (r : ZMod d) (X Y : Matrix (Fin d) (Fin d) ℂ) :
    prime_convolution_choi d r (X + Y) = prime_convolution_choi d r X + prime_convolution_choi d r Y := by
  have h := in1243_choi_linear d r (Finset.univ : Finset (Fin 2)) (fun _ => (1 : ℝ)) ![X,Y]
  simpa [Fin.sum_univ_two] using h

theorem in1249full_choi_smul (d : ℕ) (r : ZMod d) (c : ℝ) (X : Matrix (Fin d) (Fin d) ℂ) :
    prime_convolution_choi d r ((c : ℂ) • X) = (c : ℂ) • prime_convolution_choi d r X := by
  have h := in1243_choi_linear d r (Finset.univ : Finset (Fin 1)) (fun _ => c) ![X]
  simpa [Fin.sum_univ_one] using h

theorem in1249full_critical_separable
    (n : ℕ) (hp : (n+2).Prime) (h5 : 5 ≤ n+2)
    (r : Fin (n+2)) (hr0 : r ≠ 0) (hr1 : r ≠ 1) (hr2 : 2*r ≠ 1)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    matrix_is_separable (n+2) (n+2)
      (prime_convolution_choi (n+2) r (prime_convolution_critical_env (n+2) p)) := by
  obtain ⟨a,b,w,hw,heq⟩ := in1249full_critical_orbit_decomposition n hp h5 r hr0 hr1 hr2 p hp0 hp1
  rw [heq, in1249full_choi_add (n+2) (r : ZMod (n+2))]
  apply in1243_sep_add
  · exact in1243_twirl_sep n r a b
  · exact in1249full_diag_choi_sep n r w hw

theorem in1249full_threshold_sufficient
    (n : ℕ) (hp : (n+2).Prime) (h5 : 5 ≤ n+2)
    (r : Fin (n+2)) (hr0 : r ≠ 0) (hr1 : r ≠ 1) (hr2 : 2*r ≠ 1)
    (p t : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ht0 : 0 ≤ t)
    (ht : t ≤ 1 / (1 + (n+2 : ℕ) * Real.sqrt (p*(1-p)))) :
    matrix_is_separable (n+2) (n+2)
      (prime_convolution_choi (n+2) r (two_level_environment (n+2) p t)) := by
  classical
  let q := Real.sqrt (p*(1-p))
  let c : ℝ := (1-t)/(n+2 : ℕ) - t*q
  have hq : 0 ≤ q := Real.sqrt_nonneg _
  have hd : (0 : ℝ) < (n+2 : ℕ) := by exact_mod_cast (by omega : 0 < n+2)
  have hc : 0 ≤ c := by
    have hb : 0 < 1 + ((n+2 : ℕ) : ℝ)*q := by positivity
    have ht'' : t ≤ 1 / (1 + ((n+2 : ℕ) : ℝ)*q) := by simpa [q] using ht
    have ht' := (le_div_iff₀ hb).mp ht'' 
    dsimp [c]
    rw [sub_nonneg, le_div_iff₀ hd]
    push_cast at *
    nlinarith
  have henv : two_level_environment (n+2) p t =
      (t : ℂ) • prime_convolution_critical_env (n+2) p +
      Matrix.diagonal (fun _ => (c : ℂ)) := by
    ext j l
    simp only [two_level_environment, prime_convolution_critical_env, two_level_psi,
      Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.diagonal_apply,
      smul_eq_mul]
    set u : ℝ := if (j : ℕ) = 0 then Real.sqrt p else if (j : ℕ) = 1 then Real.sqrt (1-p) else 0
    set v : ℝ := if (l : ℕ) = 0 then Real.sqrt p else if (l : ℕ) = 1 then Real.sqrt (1-p) else 0
    dsimp [c,q]
    by_cases h : j=l <;> simp [h] <;> push_cast <;> ring
  rw [henv, in1249full_choi_add (n+2) (r : ZMod (n+2)), in1249full_choi_smul (n+2) (r : ZMod (n+2))]
  apply in1243_sep_add
  · exact in1243_sep_smul _ _ t ht0 _ (in1249full_critical_separable n hp h5 r hr0 hr1 hr2 p hp0 hp1)
  · exact in1249full_diag_choi_sep n r (fun _ => c) (fun _ => hc)

theorem prime_convolution_entanglement_breaking_iff_threshold :
    ∀ d : ℕ, d.Prime → 5 ≤ d → ∀ r : ZMod d, r ≠ 0 → r ≠ 1 → 2 * r ≠ 1 →
      ∀ p t : ℝ, 0 ≤ p → p ≤ 1 → 0 ≤ t → t ≤ 1 →
        (matrix_is_separable d d (prime_convolution_choi d r (two_level_environment d p t)) ↔
          t ≤ 1 / (1 + d * Real.sqrt (p * (1 - p)))) := by
  intro d hp h5 r hr0 hr1 hr2 p t hp0 hp1 ht0 ht1
  constructor
  · exact prime_convolution_separable_imp_threshold d hp h5 r hr0 hr1 hr2 p t hp0 hp1 ht0 ht1
  · intro ht
    obtain ⟨n,rfl⟩ : ∃ n, d = n+2 := ⟨d-2, by omega⟩
    exact in1249full_threshold_sufficient n hp h5 r hr0 hr1 hr2 p t hp0 hp1 ht0 ht
