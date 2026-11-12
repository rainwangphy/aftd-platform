import AFTD.Prelude
import AFTD.Kb.Tcs.V

/-!
# qutrit_rank_four_four_products_of_spectral_completion

Topic: quantum   Node: e5bbfd72c33b

Provenance: helper lemma. Helper for OP-693, in the rank-four normal-completion route related to https://arxiv.org/abs/0903.0090.

A real orthogonal spectral decomposition of the bordered normal completion yields four real-qutrit product terms for the normalized rank-four PPT block.
-/

open Matrix
open scoped BigOperators Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
-- The normality of a symmetric bordered block reduces to its first row.
private lemma in767_finalbridge_bordered_normality
    (B : Matrix (Fin 3) (Fin 3) ℂ)
    (W : Matrix (Fin 3) (Fin 1) ℂ)
    (Z : Matrix (Fin 1) (Fin 1) ℂ)
    (h11 : Bᴴ * B + W.transposeᴴ * W.transpose = B * Bᴴ + W * Wᴴ)
    (h12 : Bᴴ * W + W.transposeᴴ * Z = B * W.transposeᴴ + W * Zᴴ) :
    let N := Matrix.fromBlocks B W W.transpose Z
    Nᴴ * N = N * Nᴴ := by
  dsimp only
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  have h21 : Wᴴ * B + Zᴴ * W.transpose = W.transpose * Bᴴ + Z * Wᴴ := by
    have h := congrArg Matrix.conjTranspose h12
    simpa [Matrix.conjTranspose_add, Matrix.conjTranspose_mul] using h
  have h22 : Wᴴ * W + Zᴴ * Z = W.transpose * W.transposeᴴ + Z * Zᴴ := by
    ext i j
    fin_cases i
    fin_cases j
    simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_one,
      Matrix.conjTranspose_apply, Matrix.transpose_apply]
    simp only [Fin.sum_univ_three]
    simp only [Fin.eq_zero]
    ring
  rw [h11, h12, h21, h22]

private lemma in767_finalbridge_bordered_h11
    (B : Matrix (Fin 3) (Fin 3) ℂ) (u : Fin 3 → ℂ) (ξ : ℂ)
    (hB : B.transpose = B)
    (hC : ∀ i j, star ((Bᴴ * B + vecMulVec u (star u)) i j) =
      (Bᴴ * B + vecMulVec u (star u)) i j)
    (hξ : ξ * star ξ = 1) :
    let W : Matrix (Fin 3) (Fin 1) ℂ := fun i _ => ξ * star (u i)
    Bᴴ * B + W.transposeᴴ * W.transpose = B * Bᴴ + W * Wᴴ := by
  dsimp only
  ext i j
  have hs (a b : Fin 3) : B a b = B b a := by
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M b a) hB
    simpa only [Matrix.transpose_apply] using h
  have hh := hC i j
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.vecMulVec_apply, Pi.star_apply, star_add, star_sum, star_mul, star_star] at hh
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply, Fin.sum_univ_one]
  dsimp [Matrix.transpose_apply, Matrix.conjTranspose_apply, Matrix.mul_apply]
  change (∑ k, star (B k i) * B k j) + star (ξ * star (u i)) * (ξ * star (u j)) =
    (∑ k, B i k * star (B j k)) + (ξ * star (u i)) * star (ξ * star (u j))
  simp only [hs i, hs j]
  simp only [star_mul, star_star]
  have hsum : (∑ k, star (B k j) * B k i) =
      ∑ k, B k i * star (B k j) := by
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hsum] at hh
  linear_combination -hh + (u i * star (u j) - star (u i) * u j) * hξ

private lemma in767_finalbridge_bordered_h12
    (R S : Matrix (Fin 3) (Fin 3) ℝ) (x y : Fin 3 → ℝ) (a b : ℝ)
    (hR : R.transpose = R) (hS : S.transpose = S)
    (hxy : ∀ i, (R.mulVec y) i - (S.mulVec x) i + b*x i - a*y i = 0) :
    let B : Matrix (Fin 3) (Fin 3) ℂ := fun i j => (R i j : ℂ) + Complex.I * (S i j : ℂ)
    let W : Matrix (Fin 3) (Fin 1) ℂ := fun i _ => (x i : ℂ) + Complex.I * (y i : ℂ)
    let Z : Matrix (Fin 1) (Fin 1) ℂ := fun _ _ => (a : ℂ) + Complex.I * (b : ℂ)
    Bᴴ * W + W.transposeᴴ * Z = B * W.transposeᴴ + W * Zᴴ := by
  dsimp only
  ext i j
  fin_cases j
  have hr (k : Fin 3) : R k i = R i k := by
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M i k) hR
    simpa only [Matrix.transpose_apply] using h
  have hs (k : Fin 3) : S k i = S i k := by
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M i k) hS
    simpa only [Matrix.transpose_apply] using h
  have hh := hxy i
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at hh
  apply Complex.ext <;>
    simp [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_three, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      hr, hs] <;> linarith

private lemma in767_finalbridge_bordered_completion
    (B : Matrix (Fin 3) (Fin 3) ℂ) (u : Fin 3 → ℂ) (ξ : ℂ)
    (R S : Matrix (Fin 3) (Fin 3) ℝ) (x y : Fin 3 → ℝ) (a b : ℝ)
    (hB : B.transpose = B)
    (hRS : ∀ i j, B i j = (R i j : ℂ) + Complex.I * (S i j : ℂ))
    (hR : R.transpose = R) (hS : S.transpose = S)
    (hC : ∀ i j, star ((Bᴴ * B + vecMulVec u (star u)) i j) =
      (Bᴴ * B + vecMulVec u (star u)) i j)
    (hξ : ξ * star ξ = 1)
    (huw : ∀ i, ξ * star (u i) = (x i : ℂ) + Complex.I * (y i : ℂ))
    (hxy : ∀ i, (R.mulVec y) i - (S.mulVec x) i + b*x i - a*y i = 0) :
    let W : Matrix (Fin 3) (Fin 1) ℂ := fun i _ => ξ * star (u i)
    let Z : Matrix (Fin 1) (Fin 1) ℂ := fun _ _ => (a : ℂ) + Complex.I * (b : ℂ)
    let N := Matrix.fromBlocks B W W.transpose Z
    Nᴴ * N = N * Nᴴ := by
  dsimp only
  apply in767_finalbridge_bordered_normality
  · exact in767_finalbridge_bordered_h11 B u ξ hB hC hξ
  · have h := in767_finalbridge_bordered_h12 R S x y a b hR hS hxy
    have hb : B = fun i j => (R i j : ℂ) + Complex.I * (S i j : ℂ) := by
      ext i j
      exact hRS i j
    have hw : (fun (i : Fin 3) (_ : Fin 1) => ξ * star (u i)) =
        (fun (i : Fin 3) (_ : Fin 1) => (x i : ℂ) + Complex.I * (y i : ℂ)) := by
      funext i j
      exact huw i
    simpa only [hb, hw] using h


private lemma in767_finalbridge_bordered_phase_completion
    (B : Matrix (Fin 3) (Fin 3) ℂ) (u : Fin 3 → ℂ) (c s a b : ℝ)
    (hB : B.transpose = B)
    (hC : ∀ i j, star ((Bᴴ * B + vecMulVec u (star u)) i j) =
      (Bᴴ * B + vecMulVec u (star u)) i j)
    (hunit : c*c + s*s = 1)
    (hphase : let R : Matrix (Fin 3) (Fin 3) ℝ := fun i j => (B i j).re
      let S : Matrix (Fin 3) (Fin 3) ℝ := fun i j => (B i j).im
      let x0 : Fin 3 → ℝ := fun i => (star (u i)).re
      let y0 : Fin 3 → ℝ := fun i => (star (u i)).im
      ∀ i, (R.mulVec (fun j => s*x0 j + c*y0 j)) i -
        (S.mulVec (fun j => c*x0 j - s*y0 j)) i +
          b*(c*x0 i - s*y0 i) - a*(s*x0 i + c*y0 i) = 0) :
    let ξ : ℂ := (c : ℂ) + Complex.I * (s : ℂ)
    let W : Matrix (Fin 3) (Fin 1) ℂ := fun i _ => ξ * star (u i)
    let Z : Matrix (Fin 1) (Fin 1) ℂ := fun _ _ => (a : ℂ) + Complex.I * (b : ℂ)
    let N := Matrix.fromBlocks B W W.transpose Z
    Nᴴ * N = N * Nᴴ := by
  dsimp only
  let R : Matrix (Fin 3) (Fin 3) ℝ := fun i j => (B i j).re
  let S : Matrix (Fin 3) (Fin 3) ℝ := fun i j => (B i j).im
  let x : Fin 3 → ℝ := fun i => c * (star (u i)).re - s * (star (u i)).im
  let y : Fin 3 → ℝ := fun i => s * (star (u i)).re + c * (star (u i)).im
  have hsym (i j : Fin 3) : B i j = B j i := by
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M j i) hB
    simpa only [Matrix.transpose_apply] using h
  have hR : R.transpose = R := by
    ext i j
    exact congrArg Complex.re (hsym j i)
  have hS : S.transpose = S := by
    ext i j
    exact congrArg Complex.im (hsym j i)
  have hRS : ∀ i j, B i j = (R i j : ℂ) + Complex.I * (S i j : ℂ) := by
    intro i j
    dsimp [R, S]
    simpa only [mul_comm] using (Complex.re_add_im (B i j)).symm
  have hξ : ((c : ℂ) + Complex.I * (s : ℂ)) * star ((c : ℂ) + Complex.I * (s : ℂ)) = 1 := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> linarith
  have huw : ∀ i, ((c : ℂ) + Complex.I * (s : ℂ)) * star (u i) =
      (x i : ℂ) + Complex.I * (y i : ℂ) := by
    intro i
    apply Complex.ext <;> simp [x, y, Complex.mul_re, Complex.mul_im] <;> ring
  exact in767_finalbridge_bordered_completion B u _ R S x y a b hB hRS hR hS hC hξ huw hphase

private lemma in767_finalbridge_bordered_lower_block
    (B : Matrix (Fin 3) (Fin 3) ℂ) (u : Fin 3 → ℂ) (ξ : ℂ)
    (hB : B.transpose = B)
    (hC : ∀ i j, star ((Bᴴ * B + vecMulVec u (star u)) i j) =
      (Bᴴ * B + vecMulVec u (star u)) i j)
    (hξ : ξ * star ξ = 1) :
    let W : Matrix (Fin 3) (Fin 1) ℂ := fun i _ => ξ * star (u i)
    Bᴴ * B + vecMulVec u (star u) = B * Bᴴ + W * Wᴴ := by
  dsimp only
  have h := in767_finalbridge_bordered_h11 B u ξ hB hC hξ
  dsimp only at h
  have hW : ((fun (i : Fin 3) (_ : Fin 1) => ξ * star (u i))ᵀᴴ *
      (fun (i : Fin 3) (_ : Fin 1) => ξ * star (u i))ᵀ) = vecMulVec u (star u) := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply,
      Matrix.vecMulVec_apply, Pi.star_apply, Fin.sum_univ_one, star_mul, star_star]
    linear_combination (u i * star (u j)) * hξ
  rw [hW] at h
  exact h


private lemma in767_finalbridge_product_frame_of_diagonal
    (B C : Matrix (Fin 3) (Fin 3) ℂ) (O : Matrix (Fin 3) (Fin 4) ℝ) (lam : Fin 4 → ℂ)
    (hO : O * O.transpose = 1)
    (hB : ∀ i j, B i j = ∑ k, (O i k : ℂ) * lam k * (O j k : ℂ))
    (hC : ∀ i j, C i j = ∑ k, (O i k : ℂ) * (lam k * star (lam k)) * (O j k : ℂ)) :
    ∃ (v : Fin 4 → Fin 3 → ℂ) (a b : Fin 4 → ℂ),
      (∀ t i, star (v t i) = v t i) ∧
      (1 : Matrix (Fin 3) (Fin 3) ℂ) =
        ∑ t, (a t * star (a t)) • vecMulVec (v t) (star (v t)) ∧
      B = ∑ t, (a t * star (b t)) • vecMulVec (v t) (star (v t)) ∧
      C = ∑ t, (b t * star (b t)) • vecMulVec (v t) (star (v t)) := by
  refine ⟨fun t i => (O i t : ℂ), fun _ => 1, fun t => star (lam t), ?_, ?_, ?_, ?_⟩
  · intro t i
    simp
  · ext i j
    have hr := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M i j) hO
    simp only [Matrix.mul_apply, Matrix.transpose_apply] at hr
    have hc : (∑ k, (O i k : ℂ) * (O j k : ℂ)) = ((1 : Matrix (Fin 3) (Fin 3) ℝ) i j : ℂ) := by
      exact_mod_cast hr
    by_cases hij : i = j <;>
      simpa [hij, Matrix.vecMulVec_apply, Matrix.one_apply, Matrix.sum_apply, Matrix.smul_apply,
        mul_comm, mul_left_comm, mul_assoc] using hc.symm
  · ext i j
    simpa [Matrix.vecMulVec_apply, Matrix.sum_apply, Matrix.smul_apply,
      mul_comm, mul_left_comm, mul_assoc] using hB i j
  · ext i j
    simpa [Matrix.vecMulVec_apply, Matrix.sum_apply, Matrix.smul_apply,
      mul_comm, mul_left_comm, mul_assoc] using hC i j


private lemma in767_finalbridge_real_diagonal_normal_square
    {m : Type} [Fintype m] [DecidableEq m]
    (Q : Matrix m (Fin 4) ℂ) (lam : Fin 4 → ℂ)
    (hreal : Qᴴ = Q.transpose) (horth : Q.transpose * Q = 1) :
    let N := Q * Matrix.diagonal lam * Q.transpose
    N * Nᴴ = Q * Matrix.diagonal (fun k => lam k * star (lam k)) * Q.transpose := by
  dsimp only
  have hreal' : Q.transposeᴴ = Q := by
    rw [← hreal, Matrix.conjTranspose_conjTranspose]
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.diagonal_conjTranspose,
    hreal', hreal]
  simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Q.transpose Q,
    horth, Matrix.one_mul, Matrix.diagonal_mul_diagonal]
  rw [← Matrix.mul_assoc (Matrix.diagonal lam) (Matrix.diagonal (star lam)) Q.transpose, Matrix.diagonal_mul_diagonal]
  rfl


private lemma in767_finalbridge_spectral_frame_bridge
    (B C : Matrix (Fin 3) (Fin 3) ℂ)
    (W : Matrix (Fin 3) (Fin 1) ℂ) (Z : Matrix (Fin 1) (Fin 1) ℂ)
    (O : Matrix (Fin 3 ⊕ Fin 1) (Fin 4) ℝ) (lam : Fin 4 → ℂ)
    (horth : O.transpose * O = 1) (hcoorth : O * O.transpose = 1)
    (hC : C = B*Bᴴ + W*Wᴴ)
    (hN : let Q : Matrix (Fin 3 ⊕ Fin 1) (Fin 4) ℂ := fun i j => O i j
      Matrix.fromBlocks B W W.transpose Z = Q * Matrix.diagonal lam * Q.transpose) :
    ∃ (v : Fin 4 → Fin 3 → ℂ) (a b : Fin 4 → ℂ),
      (∀ t i, star (v t i) = v t i) ∧
      (1 : Matrix (Fin 3) (Fin 3) ℂ) =
        ∑ t, (a t * star (a t)) • vecMulVec (v t) (star (v t)) ∧
      B = ∑ t, (a t * star (b t)) • vecMulVec (v t) (star (v t)) ∧
      C = ∑ t, (b t * star (b t)) • vecMulVec (v t) (star (v t)) := by
  let Q : Matrix (Fin 3 ⊕ Fin 1) (Fin 4) ℂ := fun i j => O i j
  let V : Matrix (Fin 3) (Fin 4) ℝ := fun i j => O (Sum.inl i) j
  have hV : V * V.transpose = 1 := by
    ext i j
    have hh := congrArg (fun M : Matrix (Fin 3 ⊕ Fin 1) (Fin 3 ⊕ Fin 1) ℝ =>
      M (Sum.inl i) (Sum.inl j)) hcoorth
    simpa [V, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using hh
  have hQreal : Qᴴ = Q.transpose := by
    ext i j
    simp [Q, Matrix.conjTranspose_apply, Matrix.transpose_apply]
  have hQorth : Q.transpose * Q = 1 := by
    ext i j
    have hh := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M i j) horth
    simp only [Matrix.mul_apply, Matrix.transpose_apply] at hh
    change (∑ k : Fin 3 ⊕ Fin 1, (O k i : ℂ) * (O k j : ℂ)) = (1 : Matrix (Fin 4) (Fin 4) ℂ) i j
    by_cases hij : i = j
    · subst j
      have hh' : (∑ k : Fin 3 ⊕ Fin 1, O k i * O k i) = (1 : ℝ) := by simpa [Matrix.one_apply] using hh
      simpa [Matrix.one_apply] using (show (∑ k : Fin 3 ⊕ Fin 1, (O k i : ℂ) * (O k i : ℂ)) = 1 by exact_mod_cast hh')
    · have hh' : (∑ k : Fin 3 ⊕ Fin 1, O k i * O k j) = (0 : ℝ) := by simpa [Matrix.one_apply, hij] using hh
      simpa [Matrix.one_apply, hij] using (show (∑ k : Fin 3 ⊕ Fin 1, (O k i : ℂ) * (O k j : ℂ)) = 0 by exact_mod_cast hh')
  change Matrix.fromBlocks B W W.transpose Z = Q * Matrix.diagonal lam * Q.transpose at hN
  have hN2 : (Matrix.fromBlocks B W W.transpose Z) * (Matrix.fromBlocks B W W.transpose Z)ᴴ =
      Q * Matrix.diagonal (fun k => lam k * star (lam k)) * Q.transpose := by
    rw [hN]
    exact in767_finalbridge_real_diagonal_normal_square Q lam hQreal hQorth
  have hm (f : Fin 4 → ℂ) (i j : Fin 3 ⊕ Fin 1) :
      (Q * Matrix.diagonal f * Q.transpose) i j =
        ∑ k, (O i k : ℂ) * f k * (O j k : ℂ) := by
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Q]
  apply in767_finalbridge_product_frame_of_diagonal B C V lam hV
  · intro i j
    have hh := congrArg (fun M : Matrix (Fin 3 ⊕ Fin 1) (Fin 3 ⊕ Fin 1) ℂ =>
      M (Sum.inl i) (Sum.inl j)) hN
    simpa only [Matrix.fromBlocks_apply₁₁, hm, V] using hh
  · intro i j
    have hh := congrArg (fun M : Matrix (Fin 3 ⊕ Fin 1) (Fin 3 ⊕ Fin 1) ℂ =>
      M (Sum.inl i) (Sum.inl j)) hN2
    rw [hC]
    simpa only [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_apply₁₁, hm, V] using hh

theorem qutrit_rank_four_four_products_of_spectral_completion
    (B : Matrix (Fin 3) (Fin 3) ℂ) (u : Fin 3 → ℂ) (ξ : ℂ)
    (Z : Matrix (Fin 1) (Fin 1) ℂ)
    (O : Matrix (Fin 3 ⊕ Fin 1) (Fin 4) ℝ) (lam : Fin 4 → ℂ)
    (hB : B.transpose = B)
    (hC : ∀ i j, star ((Bᴴ * B + vecMulVec u (star u)) i j) =
      (Bᴴ * B + vecMulVec u (star u)) i j)
    (hξ : ξ * star ξ = 1)
    (horth : O.transpose * O = 1) (hcoorth : O * O.transpose = 1)
    (hN : let W : Matrix (Fin 3) (Fin 1) ℂ := fun i _ => ξ * star (u i)
      let Q : Matrix (Fin 3 ⊕ Fin 1) (Fin 4) ℂ := fun i j => O i j
      Matrix.fromBlocks B W W.transpose Z = Q * Matrix.diagonal lam * Q.transpose) :
    ∃ (v : Fin 4 → Fin 3 → ℂ) (a b : Fin 4 → ℂ),
      (∀ t i, star (v t i) = v t i) ∧
      (1 : Matrix (Fin 3) (Fin 3) ℂ) =
        ∑ t, (a t * star (a t)) • vecMulVec (v t) (star (v t)) ∧
      B = ∑ t, (a t * star (b t)) • vecMulVec (v t) (star (v t)) ∧
      Bᴴ * B + vecMulVec u (star u) =
        ∑ t, (b t * star (b t)) • vecMulVec (v t) (star (v t)) := by
  let W : Matrix (Fin 3) (Fin 1) ℂ := fun i _ => ξ * star (u i)
  apply in767_finalbridge_spectral_frame_bridge B (Bᴴ * B + vecMulVec u (star u)) W Z O lam horth hcoorth
  · exact in767_finalbridge_bordered_lower_block B u ξ hB hC hξ
  · exact hN
