import AFTD.Prelude

/-!
# qutrit_fixed_phase_schur_four_product_decomposition

Topic: quantum   Node: a46f792c11bd

Provenance: helper lemma. Degenerate-branch helper for the rank-four source in OP-693.

A qutrit block with a real orthogonal complex spectral basis and a fixed-phase Schur vector has a four-term product decomposition.
-/

open Matrix
open scoped BigOperators Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
private lemma in767_fixedproof_fixed_spectral_square
    (Q : Matrix (Fin 3) (Fin 3) ℂ) (lam : Fin 3 → ℂ)
    (hreal : Qᴴ = Q.transpose) (horth : Q.transpose * Q = 1) :
    let B := Q * Matrix.diagonal lam * Q.transpose
    Bᴴ * B = Q * Matrix.diagonal (fun k => star (lam k) * lam k) * Q.transpose := by
  dsimp only
  have hreal' : Q.transposeᴴ = Q := by
    rw [← hreal, Matrix.conjTranspose_conjTranspose]
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.diagonal_conjTranspose,
    hreal', hreal]
  simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Q.transpose Q, horth, Matrix.one_mul]
  rw [← Matrix.mul_assoc (Matrix.diagonal (star lam)) (Matrix.diagonal lam) Q.transpose,
    Matrix.diagonal_mul_diagonal]
  rfl

private lemma in767_fixedproof_fixed_phase_product_expansion
    (B : Matrix (Fin 3) (Fin 3) ℂ) (u : Fin 3 → ℂ)
    (O : Matrix (Fin 3) (Fin 3) ℝ) (lam : Fin 3 → ℂ)
    (v0 : Fin 3 → ℝ) (gamma : ℂ)
    (horth : O.transpose * O = 1) (hcoorth : O * O.transpose = 1)
    (hB : ∀ i j, B i j = ∑ k, (O i k : ℂ) * lam k * (O j k : ℂ))
    (hu : ∀ i, u i = gamma * (v0 i : ℂ)) :
    ∃ (v : Fin 4 → Fin 3 → ℂ) (a b : Fin 4 → ℂ),
      (∀ t i, star (v t i) = v t i) ∧
      (1 : Matrix (Fin 3) (Fin 3) ℂ) =
        ∑ t, (a t * star (a t)) • vecMulVec (v t) (star (v t)) ∧
      B = ∑ t, (a t * star (b t)) • vecMulVec (v t) (star (v t)) ∧
      Bᴴ * B + vecMulVec u (star u) =
        ∑ t, (b t * star (b t)) • vecMulVec (v t) (star (v t)) := by
  let Q : Matrix (Fin 3) (Fin 3) ℂ := fun i j => O i j
  have hQreal : Qᴴ = Q.transpose := by ext i j; simp [Q, Matrix.conjTranspose_apply, Matrix.transpose_apply]
  have hQorth : Q.transpose * Q = 1 := by
    ext i j
    have hh := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M i j) horth
    simp only [Matrix.mul_apply, Matrix.transpose_apply] at hh
    change (∑ k : Fin 3, (O k i : ℂ) * (O k j : ℂ)) = (1 : Matrix (Fin 3) (Fin 3) ℂ) i j
    by_cases hij : i=j
    · subst j
      have hh' : (∑ k : Fin 3, O k i * O k i) = (1 : ℝ) := by simpa [Matrix.one_apply] using hh
      simpa [Matrix.one_apply] using (show (∑ k : Fin 3, (O k i : ℂ) * (O k i : ℂ)) = 1 by exact_mod_cast hh')
    · have hh' : (∑ k : Fin 3, O k i * O k j) = (0 : ℝ) := by simpa [Matrix.one_apply,hij] using hh
      simpa [Matrix.one_apply,hij] using (show (∑ k : Fin 3, (O k i : ℂ) * (O k j : ℂ)) = 0 by exact_mod_cast hh')
  have hBmat : B = Q*Matrix.diagonal lam*Q.transpose := by
    ext i j
    rw [Matrix.mul_apply]
    simpa only [Matrix.mul_diagonal, Matrix.transpose_apply, Q] using hB i j
  have hBsq : Bᴴ*B = Q * Matrix.diagonal (fun k => star (lam k) * lam k) * Q.transpose := by
    rw [hBmat]
    exact in767_fixedproof_fixed_spectral_square Q lam hQreal hQorth
  let v : Fin 4 → Fin 3 → ℂ := fun t i =>
    if t=0 then O i 0 else if t=1 then O i 1 else if t=2 then O i 2 else v0 i
  let a : Fin 4 → ℂ := fun t => if t=3 then 0 else 1
  let b : Fin 4 → ℂ := fun t => if t=0 then star (lam 0) else if t=1 then star (lam 1)
    else if t=2 then star (lam 2) else gamma
  refine ⟨v,a,b,?_,?_,?_,?_⟩
  · intro t i
    fin_cases t <;> simp [v]
  · ext i j
    have hh := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M i j) hcoorth
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three] at hh
    have hh' : (∑ k : Fin 3, (O i k : ℂ)*(O j k : ℂ)) = (1 : Matrix (Fin 3) (Fin 3) ℂ) i j := by
      by_cases hij : i=j
      · subst j
        have hh' : (O i 0)^2+(O i 1)^2+(O i 2)^2 = (1:ℝ) := by simpa [Matrix.one_apply,pow_two] using hh
        simpa [Matrix.one_apply,Fin.sum_univ_three,pow_two] using (show (O i 0 : ℂ)^2+(O i 1 : ℂ)^2+(O i 2 : ℂ)^2=1 by exact_mod_cast hh')
      · have hh' : O i 0*O j 0+O i 1*O j 1+O i 2*O j 2=(0:ℝ) := by simpa [Matrix.one_apply,hij] using hh
        simpa [Matrix.one_apply,hij,Fin.sum_univ_three] using (show (O i 0 : ℂ)*(O j 0 : ℂ)+(O i 1 : ℂ)*(O j 1 : ℂ)+(O i 2 : ℂ)*(O j 2 : ℂ)=0 by exact_mod_cast hh')
    simpa [v,a,b,Matrix.sum_apply,Matrix.smul_apply,Matrix.vecMulVec_apply,
      Fin.sum_univ_four,Fin.sum_univ_three,Complex.real_smul,mul_comm,mul_left_comm,mul_assoc] using hh'.symm
  · ext i j
    simpa [v,a,b,Matrix.sum_apply,Matrix.smul_apply,Matrix.vecMulVec_apply,
      Fin.sum_univ_four,Fin.sum_univ_three,Complex.real_smul,mul_comm,mul_left_comm,mul_assoc] using hB i j
  · ext i j
    have hh := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M i j) hBsq
    have hm : (Q * Matrix.diagonal (fun k => star (lam k)*lam k) * Q.transpose) i j =
        ∑ k : Fin 3, (O i k : ℂ) * (star (lam k)*lam k) * (O j k : ℂ) := by
      rw [Matrix.mul_apply]
      simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Q]
    rw [hm] at hh
    simp only [Fin.sum_univ_three] at hh
    simp [v,a,b,Matrix.sum_apply,Matrix.smul_apply,Matrix.vecMulVec_apply,
      Fin.sum_univ_four,Complex.real_smul,hu,Matrix.add_apply, hh,
      mul_comm,mul_left_comm,mul_assoc]

theorem qutrit_fixed_phase_schur_four_product_decomposition :
  ∀ (B : Matrix (Fin 3) (Fin 3) ℂ) (u : Fin 3 → ℂ)
    (O : Matrix (Fin 3) (Fin 3) ℝ) (lam : Fin 3 → ℂ)
    (v0 : Fin 3 → ℝ) (gamma : ℂ),
    O.transpose * O = 1 → O * O.transpose = 1 →
    (∀ i j, B i j = ∑ k, (O i k : ℂ) * lam k * (O j k : ℂ)) →
    (∀ i, u i = gamma * (v0 i : ℂ)) →
    ∃ (v : Fin 4 → Fin 3 → ℂ) (a b : Fin 4 → ℂ),
      (∀ t i, star (v t i) = v t i) ∧
      (1 : Matrix (Fin 3) (Fin 3) ℂ) =
        ∑ t, (a t * star (a t)) • vecMulVec (v t) (star (v t)) ∧
      B = ∑ t, (a t * star (b t)) • vecMulVec (v t) (star (v t)) ∧
      Bᴴ * B + vecMulVec u (star u) =
        ∑ t, (b t * star (b t)) • vecMulVec (v t) (star (v t)) := by
  intro B u O lam v0 gamma horth hcoorth hB hu
  exact in767_fixedproof_fixed_phase_product_expansion B u O lam v0 gamma horth hcoorth hB hu
