import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.IsOrthonormalHermitianBasis
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.G

/-!
# hermitian_matrix_parseval_sum

Topic: quantum   Node: 97259df511fe

Provenance: helper lemma. step towards open_problem_qudit_pure_state_invariants

For any natural number d ≥ 1, any orthonormal Hermitian basis T of trace-zero matrices, and any Hermitian matrix A, the sum of squared Hilbert-Schmidt inner products with T equals Tr(A^2) - (Tr A)^2 / d.
-/

open Matrix

private lemma hermitian_matrix_parseval_sum_aux (d : ℕ)
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (u : ι → Matrix (Fin d) (Fin d) ℂ)
    (horth : ∀ i j, (u i * u j).trace = if i = j then 1 else 0)
    (hcard : Fintype.card ι = d^2) :
    ∀ A : Matrix (Fin d) (Fin d) ℂ, (A * A).trace = ∑ i, ((u i * A).trace)^2 := by
  intro A
  have hcard' : Fintype.card ι = Module.finrank ℂ (Matrix (Fin d) (Fin d) ℂ) := by
    rw [show Module.finrank ℂ (Matrix (Fin d) (Fin d) ℂ) = d^2 from by
      rw [Module.finrank_matrix]; simp [Module.finrank_self, pow_two]]
    exact hcard
  have hli : LinearIndependent ℂ u := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h := congrArg (fun X => (u i * X).trace) hg
    rw [Matrix.mul_zero, Matrix.trace_zero] at h
    have hsum : (u i * (∑ j, g j • u j)).trace = ∑ j, g j * (u i * u j).trace := by
      rw [Matrix.mul_sum]
      simp only [Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]
    rw [hsum] at h
    simp only [horth, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
      if_true] at h
    exact h
  let B : Module.Basis ι ℂ (Matrix (Fin d) (Fin d) ℂ) :=
    basisOfLinearIndependentOfCardEqFinrank hli hcard'
  have hB : (⇑B : ι → Matrix (Fin d) (Fin d) ℂ) = u := by
    simp only [B, coe_basisOfLinearIndependentOfCardEqFinrank]
  have hcoeff : ∀ i, B.repr A i = (u i * A).trace := by
    intro i
    have hkey : (u i * A).trace = ∑ j, B.repr A j * (u i * B j).trace := by
      conv_lhs => rw [← B.sum_repr A]
      rw [Matrix.mul_sum]
      simp only [Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]
    rw [hkey]
    simp only [hB, horth, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
      if_true]
  have hAexp : A = ∑ i, (u i * A).trace • u i := by
    conv_lhs => rw [← B.sum_repr A]
    simp only [hcoeff, hB]
  have hstep1 : (A * A).trace = ((∑ i, (u i * A).trace • u i) * A).trace :=
    congrArg (fun X => (X * A).trace) hAexp
  rw [hstep1, Matrix.sum_mul]
  simp only [Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, sq]

private lemma hermitian_matrix_parseval_sum_selfconj_re {z : ℂ} (hz : star z = z) :
    z = (z.re : ℂ) := by
  have him : z.im = 0 := by
    rw [← Complex.conj_eq_iff_im]
    simpa using hz
  apply Complex.ext <;> simp [him]

private lemma hermitian_matrix_parseval_sum_selfconj_sq {z : ℂ} (hz : star z = z) :
    z ^ 2 = ((z.re ^ 2 : ℝ) : ℂ) := by
  rw [hermitian_matrix_parseval_sum_selfconj_re hz, ← Complex.ofReal_pow]
  rw [Complex.ofReal_re]

/-- For any natural number d ≥ 1, any orthonormal Hermitian basis T of trace-zero matrices, and any Hermitian matrix A, the sum of squared Hilbert-Schmidt inner products with T equals Tr(A^2) - (Tr A)^2 / d. -/
theorem hermitian_matrix_parseval_sum (d : ℕ) (hd : 1 ≤ d)
    (T : Fin (d^2 - 1) → Matrix (Fin d) (Fin d) ℂ) (hT : is_orthonormal_hermitian_basis d T)
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) :
    ∑ a : Fin (d^2 - 1), (Matrix.trace (A * T a)).re ^ 2 =
      (Matrix.trace (A * A)).re - (Matrix.trace A).re ^ 2 / (d : ℝ) := by
  obtain ⟨hHerm, hTrace0, hOrth⟩ := hT
  classical
  set r : ℝ := (Real.sqrt (d:ℝ))⁻¹ with hr_def
  have hr_sq : r * r = ((d:ℝ))⁻¹ := by
    have hs : (Real.sqrt (d:ℝ))^2 = (d:ℝ) := Real.sq_sqrt (by positivity)
    rw [hr_def, ← sq, inv_pow, hs]
  have hrC_sq : (r:ℂ) * (r:ℂ) = ((d:ℂ))⁻¹ := by
    rw [← Complex.ofReal_mul, hr_sq, Complex.ofReal_inv]
    norm_num
  have hdC : (d:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  let b : Option (Fin (d^2-1)) → Matrix (Fin d) (Fin d) ℂ :=
    fun i => i.elim ((r:ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) T
  have hb_none : b none = (r:ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) := rfl
  have hb_some : ∀ a, b (some a) = T a := fun a => rfl
  have hb_orth : ∀ i j, (b i * b j).trace = if i = j then 1 else 0 := by
    intro i j
    cases i with
    | none =>
      cases j with
      | none =>
        rw [if_pos rfl, hb_none]
        have hnn : ((((r:ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) *
            ((r:ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)))).trace
            = (r:ℂ) * (r:ℂ) * (d:ℂ) := by
          rw [Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, Matrix.trace_smul,
            Matrix.trace_one]
          simp [Fintype.card_fin, smul_eq_mul]
          ring
        rw [hnn, hrC_sq, inv_mul_cancel₀ hdC]
      | some c =>
        rw [if_neg (by simp), hb_none, hb_some]
        rw [Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, hTrace0 c, smul_zero]
    | some a =>
      cases j with
      | none =>
        rw [if_neg (by simp), hb_some, hb_none]
        rw [Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, hTrace0 a, smul_zero]
      | some c =>
        simp only [hb_some]
        rw [hOrth a c]
        by_cases h : a = c
        · simp [h]
        · simp [h]
  have hb_card : Fintype.card (Option (Fin (d^2-1))) = d^2 := by
    have h1 : 1 ≤ d^2 := by nlinarith
    rw [Fintype.card_option]
    simp [Nat.sub_add_cancel h1]
  have hmain := hermitian_matrix_parseval_sum_aux d b hb_orth hb_card A
  have hbn : (b none * A).trace = (r:ℂ) * A.trace := by
    rw [hb_none, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, smul_eq_mul]
  have hbs : ∀ a, (b (some a) * A).trace = (T a * A).trace := fun a => by
    simp only [hb_some]
  have hcomplex_eq' : ∑ a : Fin (d^2-1), ((T a * A).trace)^2 =
      (A*A).trace - (A.trace)^2 / (d:ℂ) := by
    rw [Fintype.sum_option] at hmain
    rw [hbn] at hmain
    simp only [hbs] at hmain
    have hr1 : ((r:ℂ) * A.trace)^2 = (A.trace)^2 / (d:ℂ) := by
      rw [mul_pow, pow_two, hrC_sq, div_eq_inv_mul]
    rw [hr1] at hmain
    rw [eq_sub_iff_add_eq, add_comm]
    exact hmain.symm
  have hcomplex_eq : ∑ a : Fin (d^2-1), ((A * T a).trace)^2 =
      (A*A).trace - (A.trace)^2 / (d:ℂ) := by
    rw [← hcomplex_eq']
    apply Finset.sum_congr rfl
    intro a _
    rw [Matrix.trace_mul_comm (T a) A]
  have hreal_t : ∀ a, star ((A * T a).trace) = (A * T a).trace := by
    intro a
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, (hHerm a).eq, hA.eq,
      Matrix.trace_mul_comm (T a) A]
  have hreal_A : star (A.trace) = A.trace := by
    rw [← Matrix.trace_conjTranspose, hA.eq]
  have hreal_AA : star ((A * A).trace) = (A*A).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hA.eq]
  have hsq : ∀ a : Fin (d^2-1),
      ((A * T a).trace)^2 = ((((A * T a).trace).re ^ 2 : ℝ) : ℂ) :=
    fun a => hermitian_matrix_parseval_sum_selfconj_sq (hreal_t a)
  have hLHS : ((∑ a : Fin (d^2-1), ((A * T a).trace).re ^ 2 : ℝ) : ℂ) =
      (A*A).trace - (A.trace)^2 / (d:ℂ) := by
    calc ((∑ a : Fin (d^2-1), ((A * T a).trace).re ^ 2 : ℝ) : ℂ)
        = ∑ a : Fin (d^2-1), ((((A * T a).trace).re ^ 2 : ℝ) : ℂ) := by
            rw [Complex.ofReal_sum]
      _ = ∑ a : Fin (d^2-1), ((A * T a).trace)^2 :=
            Finset.sum_congr rfl fun a _ => (hsq a).symm
      _ = _ := hcomplex_eq
  have hRHS : ((((A*A).trace).re - (((A.trace).re)^2 / (d:ℝ)) : ℝ) : ℂ) =
      (A*A).trace - (A.trace)^2 / (d:ℂ) := by
    rw [Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_pow]
    rw [Complex.ofReal_natCast]
    rw [show ((((A*A).trace).re : ℝ) : ℂ) = (A*A).trace from
          (hermitian_matrix_parseval_sum_selfconj_re hreal_AA).symm,
        show ((((A.trace).re : ℝ) : ℂ)) = A.trace from
          (hermitian_matrix_parseval_sum_selfconj_re hreal_A).symm]
  rw [← Complex.ofReal_inj]
  exact hLHS.trans hRHS.symm
