import AFTD.Prelude
import AFTD.Kb.Tcs.V

/-!
# qutrit_rank_four_block_product_from_three_lemmas

Topic: quantum   Node: 58c3428a43fc

Provenance: helper lemma. Helper for OP-693, in the rank-four normal-completion route related to https://arxiv.org/abs/0903.0090.

The normalized rank-four qutrit PPT block admits four product terms, conditional on phase selection, simultaneous real orthogonal diagonalization, and a fixed-phase spectral expansion.
-/

open Matrix
open scoped BigOperators Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
-- The normality of a symmetric bordered block reduces to its first row.
private lemma in767_whole_conditional_bordered_normality
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

private lemma in767_whole_conditional_bordered_h11
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

private lemma in767_whole_conditional_bordered_h12
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

private lemma in767_whole_conditional_bordered_completion
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
  apply in767_whole_conditional_bordered_normality
  · exact in767_whole_conditional_bordered_h11 B u ξ hB hC hξ
  · have h := in767_whole_conditional_bordered_h12 R S x y a b hR hS hxy
    have hb : B = fun i j => (R i j : ℂ) + Complex.I * (S i j : ℂ) := by
      ext i j
      exact hRS i j
    have hw : (fun (i : Fin 3) (_ : Fin 1) => ξ * star (u i)) =
        (fun (i : Fin 3) (_ : Fin 1) => (x i : ℂ) + Complex.I * (y i : ℂ)) := by
      funext i j
      exact huw i
    simpa only [hb, hw] using h


private lemma in767_whole_conditional_bordered_phase_completion
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
  exact in767_whole_conditional_bordered_completion B u _ R S x y a b hB hRS hR hS hC hξ huw hphase

private lemma in767_whole_conditional_bordered_lower_block
    (B : Matrix (Fin 3) (Fin 3) ℂ) (u : Fin 3 → ℂ) (ξ : ℂ)
    (hB : B.transpose = B)
    (hC : ∀ i j, star ((Bᴴ * B + vecMulVec u (star u)) i j) =
      (Bᴴ * B + vecMulVec u (star u)) i j)
    (hξ : ξ * star ξ = 1) :
    let W : Matrix (Fin 3) (Fin 1) ℂ := fun i _ => ξ * star (u i)
    Bᴴ * B + vecMulVec u (star u) = B * Bᴴ + W * Wᴴ := by
  dsimp only
  have h := in767_whole_conditional_bordered_h11 B u ξ hB hC hξ
  dsimp only at h
  have hW : ((fun (i : Fin 3) (_ : Fin 1) => ξ * star (u i))ᵀᴴ *
      (fun (i : Fin 3) (_ : Fin 1) => ξ * star (u i))ᵀ) = vecMulVec u (star u) := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply,
      Matrix.vecMulVec_apply, Pi.star_apply, Fin.sum_univ_one, star_mul, star_star]
    linear_combination (u i * star (u j)) * hξ
  rw [hW] at h
  exact h


private lemma in767_whole_conditional_product_frame_of_diagonal
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


private lemma in767_whole_conditional_real_diagonal_normal_square
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


private lemma in767_whole_conditional_spectral_frame_bridge
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
    exact in767_whole_conditional_real_diagonal_normal_square Q lam hQreal hQorth
  have hm (f : Fin 4 → ℂ) (i j : Fin 3 ⊕ Fin 1) :
      (Q * Matrix.diagonal f * Q.transpose) i j =
        ∑ k, (O i k : ℂ) * f k * (O j k : ℂ) := by
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Q]
  apply in767_whole_conditional_product_frame_of_diagonal B C V lam hV
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


private lemma in767_whole_conditional_four_products_of_bordered_spectrum
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
  apply in767_whole_conditional_spectral_frame_bridge B (Bᴴ * B + vecMulVec u (star u)) W Z O lam horth hcoorth
  · exact in767_whole_conditional_bordered_lower_block B u ξ hB hC hξ
  · exact hN


private lemma in767_whole_conditional_normal_symmetric_parts_commute
    (N : Matrix (Fin 4) (Fin 4) ℂ) (hsym : N.transpose = N)
    (hnormal : Nᴴ * N = N * Nᴴ) :
    let R : Matrix (Fin 4) (Fin 4) ℝ := fun i j => (N i j).re
    let S : Matrix (Fin 4) (Fin 4) ℝ := fun i j => (N i j).im
    R.transpose = R ∧ S.transpose = S ∧ R*S=S*R := by
  dsimp only
  have hs (i j : Fin 4) : N i j = N j i := by
    have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M j i) hsym
    simpa only [Matrix.transpose_apply] using h
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    exact congrArg Complex.re (hs j i)
  · ext i j
    exact congrArg Complex.im (hs j i)
  · ext i j
    have hn := congrArg Complex.im (congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M i j) hnormal)
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_four,
      Complex.add_im, Complex.mul_im, Complex.star_def, Complex.conj_im, Complex.conj_re] at hn
    simp only [Matrix.mul_apply, Fin.sum_univ_four]
    simp only [hs i, hs j] at hn
    simp only [hs i, hs j]
    linarith

private lemma in767_whole_conditional_normal_symmetric_spectral_of_real_pair
    (N : Matrix (Fin 4) (Fin 4) ℂ) (hsym : N.transpose = N)
    (hnormal : Nᴴ * N = N * Nᴴ)
    (hdiag : ∀ (R S : Matrix (Fin 4) (Fin 4) ℝ),
      R.transpose = R → S.transpose = S → R*S = S*R →
      ∃ (O : Matrix (Fin 4) (Fin 4) ℝ) (r s : Fin 4 → ℝ),
        O.transpose * O = 1 ∧ O * O.transpose = 1 ∧
        R = O * Matrix.diagonal r * O.transpose ∧
        S = O * Matrix.diagonal s * O.transpose) :
    ∃ (O : Matrix (Fin 4) (Fin 4) ℝ) (lam : Fin 4 → ℂ),
      O.transpose * O = 1 ∧ O * O.transpose = 1 ∧
      let Q : Matrix (Fin 4) (Fin 4) ℂ := fun i j => O i j
      N = Q * Matrix.diagonal lam * Q.transpose := by
  obtain ⟨hR, hS, hRS⟩ := in767_whole_conditional_normal_symmetric_parts_commute N hsym hnormal
  obtain ⟨O, r, s, horth, hcoorth, hr, hi⟩ := hdiag _ _ hR hS hRS
  refine ⟨O, fun k => (r k : ℂ) + Complex.I * (s k : ℂ), horth, hcoorth, ?_⟩
  dsimp only
  ext i j
  have hr' := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M i j) hr
  have hi' := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M i j) hi
  rw [Matrix.mul_apply] at hr' hi'
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_four] at hr' hi'
  rw [Matrix.mul_apply]
  apply Complex.ext <;>
    simp [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_four,
      Complex.mul_re, Complex.mul_im] <;> linarith

private lemma in767_whole_conditional_normal_spectrum_sum_index
    (N : Matrix (Fin 3 ⊕ Fin 1) (Fin 3 ⊕ Fin 1) ℂ) (hsym : N.transpose = N)
    (hnormal : Nᴴ * N = N * Nᴴ)
    (hdiag : ∀ (R S : Matrix (Fin 4) (Fin 4) ℝ),
      R.transpose = R → S.transpose = S → R*S = S*R →
      ∃ (O : Matrix (Fin 4) (Fin 4) ℝ) (r s : Fin 4 → ℝ),
        O.transpose * O = 1 ∧ O * O.transpose = 1 ∧
        R = O * Matrix.diagonal r * O.transpose ∧
        S = O * Matrix.diagonal s * O.transpose) :
    ∃ (O : Matrix (Fin 3 ⊕ Fin 1) (Fin 4) ℝ) (lam : Fin 4 → ℂ),
      O.transpose * O = 1 ∧ O * O.transpose = 1 ∧
      let Q : Matrix (Fin 3 ⊕ Fin 1) (Fin 4) ℂ := fun i j => O i j
      N = Q * Matrix.diagonal lam * Q.transpose := by
  let e : Fin 3 ⊕ Fin 1 ≃ Fin 4 := finSumFinEquiv
  let N4 : Matrix (Fin 4) (Fin 4) ℂ := N.submatrix e.symm e.symm
  have hs4 : N4.transpose = N4 := by
    dsimp [N4]
    rw [Matrix.transpose_submatrix, hsym]
  have hn4 : N4ᴴ * N4 = N4 * N4ᴴ := by
    dsimp [N4]
    rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv Nᴴ N e.symm e.symm e.symm,
      Matrix.submatrix_mul_equiv N Nᴴ e.symm e.symm e.symm, hnormal]
  obtain ⟨O4, lam, horth, hcoorth, hspec⟩ :=
    in767_whole_conditional_normal_symmetric_spectral_of_real_pair N4 hs4 hn4 hdiag
  let O : Matrix (Fin 3 ⊕ Fin 1) (Fin 4) ℝ := fun i j => O4 (e i) j
  refine ⟨O, lam, ?_, ?_, ?_⟩
  · ext i j
    have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M i j) horth
    simp only [Matrix.mul_apply, Matrix.transpose_apply] at h ⊢
    change (∑ k : Fin 3 ⊕ Fin 1, O4 (e k) i * O4 (e k) j) = _
    calc
      _ = ∑ k : Fin 4, O4 k i * O4 k j := e.sum_comp (fun k => O4 k i * O4 k j)
      _ = _ := h
  · ext i j
    have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M (e i) (e j)) hcoorth
    simp only [Matrix.mul_apply, Matrix.transpose_apply] at h ⊢
    change (∑ k : Fin 4, O4 (e i) k * O4 (e j) k) = _
    simpa only [Matrix.one_apply, e.injective.eq_iff] using h
  · dsimp only
    ext i j
    have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M (e i) (e j)) hspec
    change N i j = _
    have hN4 : N4 (e i) (e j) = N i j := by simp [N4]
    rw [hN4] at h
    rw [Matrix.mul_apply] at h ⊢
    simpa only [Matrix.mul_diagonal, Matrix.transpose_apply, O] using h


private lemma in767_whole_conditional_rank_four_nondegenerate_from_phase_and_spectrum
    (B : Matrix (Fin 3) (Fin 3) ℂ) (u : Fin 3 → ℂ)
    (hB : B.transpose = B)
    (hC : ∀ i j, star ((Bᴴ * B + vecMulVec u (star u)) i j) =
      (Bᴴ * B + vecMulVec u (star u)) i j)
    (hli : LinearIndependent ℝ ![(fun i : Fin 3 => (star (u i)).re),
                                  (fun i : Fin 3 => (star (u i)).im)])
    (hphase : ∀ (R S : Matrix (Fin 3) (Fin 3) ℝ) (x y : Fin 3 → ℝ),
      LinearIndependent ℝ ![x, y] →
      ∃ c s a b : ℝ, c*c + s*s = 1 ∧
        ∀ i : Fin 3, (R.mulVec (fun j => s*x j + c*y j)) i -
          (S.mulVec (fun j => c*x j - s*y j)) i +
            b*(c*x i - s*y i) - a*(s*x i + c*y i) = 0)
    (hdiag : ∀ (R S : Matrix (Fin 4) (Fin 4) ℝ),
      R.transpose = R → S.transpose = S → R*S = S*R →
      ∃ (O : Matrix (Fin 4) (Fin 4) ℝ) (r s : Fin 4 → ℝ),
        O.transpose * O = 1 ∧ O * O.transpose = 1 ∧
        R = O * Matrix.diagonal r * O.transpose ∧
        S = O * Matrix.diagonal s * O.transpose) :
    ∃ (v : Fin 4 → Fin 3 → ℂ) (a b : Fin 4 → ℂ),
      (∀ t i, star (v t i) = v t i) ∧
      (1 : Matrix (Fin 3) (Fin 3) ℂ) =
        ∑ t, (a t * star (a t)) • vecMulVec (v t) (star (v t)) ∧
      B = ∑ t, (a t * star (b t)) • vecMulVec (v t) (star (v t)) ∧
      Bᴴ * B + vecMulVec u (star u) =
        ∑ t, (b t * star (b t)) • vecMulVec (v t) (star (v t)) := by
  obtain ⟨c, s, a, b, hunit, hxy⟩ := hphase (fun i j => (B i j).re)
    (fun i j => (B i j).im) (fun i => (star (u i)).re) (fun i => (star (u i)).im) hli
  let ξ : ℂ := (c : ℂ) + Complex.I * (s : ℂ)
  let W : Matrix (Fin 3) (Fin 1) ℂ := fun i _ => ξ * star (u i)
  let Z : Matrix (Fin 1) (Fin 1) ℂ := fun _ _ => (a : ℂ) + Complex.I * (b : ℂ)
  let N : Matrix (Fin 3 ⊕ Fin 1) (Fin 3 ⊕ Fin 1) ℂ := Matrix.fromBlocks B W W.transpose Z
  have hn : Nᴴ * N = N * Nᴴ := by
    exact in767_whole_conditional_bordered_phase_completion B u c s a b hB hC hunit hxy
  have hz : Z.transpose = Z := by
    ext i j
    fin_cases i
    fin_cases j
    rfl
  have hs : N.transpose = N := by
    dsimp [N]
    rw [Matrix.fromBlocks_transpose, hB, Matrix.transpose_transpose, hz]
  obtain ⟨O, lam, ho, hoc, hspec⟩ := in767_whole_conditional_normal_spectrum_sum_index N hs hn hdiag
  have hξ : ξ * star ξ = 1 := by
    dsimp [ξ]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> linarith
  exact in767_whole_conditional_four_products_of_bordered_spectrum B u ξ Z O lam hB hC hξ ho hoc hspec


private lemma in767_whole_conditional_dependent_re_im_fixed_phase (u : Fin 3 → ℂ)
    (hdep : ¬ LinearIndependent ℝ ![(fun i : Fin 3 => (star (u i)).re),
                                    (fun i : Fin 3 => (star (u i)).im)]) :
    ∃ (v : Fin 3 → ℝ) (gamma : ℂ), ∀ i, u i = gamma * (v i : ℂ) := by
  let x : Fin 3 → ℝ := fun i => (star (u i)).re
  let y : Fin 3 → ℝ := fun i => (star (u i)).im
  by_cases hx : x = 0
  · refine ⟨y, -Complex.I, ?_⟩
    intro i
    have hi := congrFun hx i
    dsimp [x] at hi
    apply Complex.ext <;> simp [y, Complex.mul_re, Complex.mul_im] at hi ⊢ <;> linarith
  · have hex : ∃ t : ℝ, t • x = y := by
      by_contra h
      apply hdep
      apply (LinearIndependent.pair_iff' hx).2
      intro t ht
      exact h ⟨t, ht⟩
    obtain ⟨t, ht⟩ := hex
    refine ⟨x, 1 - Complex.I * (t : ℂ), ?_⟩
    intro i
    have hi := congrFun ht i
    dsimp [x, y] at hi
    apply Complex.ext <;> simp [x, Complex.mul_re, Complex.mul_im] at hi ⊢ <;> linarith

private lemma in767_whole_conditional_fixed_phase_block_normal
    (B : Matrix (Fin 3) (Fin 3) ℂ) (u : Fin 3 → ℂ)
    (v : Fin 3 → ℝ) (gamma : ℂ)
    (hB : B.transpose = B) (hu : ∀ i, u i = gamma * (v i : ℂ))
    (hC : ∀ i j, star ((Bᴴ * B + vecMulVec u (star u)) i j) =
      (Bᴴ * B + vecMulVec u (star u)) i j) :
    Bᴴ * B = B * Bᴴ := by
  have hs (i j : Fin 3) : B i j = B j i := by
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M j i) hB
    simpa only [Matrix.transpose_apply] using h
  have hup (i j : Fin 3) : u i * star (u j) = u j * star (u i) := by
    rw [hu i, hu j]
    simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
    ring
  ext i j
  have hh := hC i j
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.vecMulVec_apply, Pi.star_apply, star_add, star_sum, star_mul, star_star] at hh
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  simp only [hs i, hs j]
  have hsum : (∑ k, star (B k j) * B k i) = ∑ k, B k i * star (B k j) := by
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hsum] at hh
  have huij := hup i j
  linear_combination -hh - huij


private lemma in767_whole_conditional_normal_symmetric_parts_commute_three
    (N : Matrix (Fin 3) (Fin 3) ℂ) (hsym : N.transpose = N)
    (hnormal : Nᴴ * N = N * Nᴴ) :
    let R : Matrix (Fin 3) (Fin 3) ℝ := fun i j => (N i j).re
    let S : Matrix (Fin 3) (Fin 3) ℝ := fun i j => (N i j).im
    R.transpose = R ∧ S.transpose = S ∧ R*S=S*R := by
  dsimp only
  have hs (i j : Fin 3) : N i j = N j i := by
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M j i) hsym
    simpa only [Matrix.transpose_apply] using h
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    exact congrArg Complex.re (hs j i)
  · ext i j
    exact congrArg Complex.im (hs j i)
  · ext i j
    have hn := congrArg Complex.im (congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M i j) hnormal)
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_three,
      Complex.add_im, Complex.mul_im, Complex.star_def, Complex.conj_im, Complex.conj_re] at hn
    simp only [Matrix.mul_apply, Fin.sum_univ_three]
    simp only [hs i, hs j] at hn
    simp only [hs i, hs j]
    linarith

private lemma in767_whole_conditional_normal_symmetric_spectral_of_real_pair_three
    (N : Matrix (Fin 3) (Fin 3) ℂ) (hsym : N.transpose = N)
    (hnormal : Nᴴ * N = N * Nᴴ)
    (hdiag : ∀ (R S : Matrix (Fin 3) (Fin 3) ℝ),
      R.transpose = R → S.transpose = S → R*S = S*R →
      ∃ (O : Matrix (Fin 3) (Fin 3) ℝ) (r s : Fin 3 → ℝ),
        O.transpose * O = 1 ∧ O * O.transpose = 1 ∧
        R = O * Matrix.diagonal r * O.transpose ∧
        S = O * Matrix.diagonal s * O.transpose) :
    ∃ (O : Matrix (Fin 3) (Fin 3) ℝ) (lam : Fin 3 → ℂ),
      O.transpose * O = 1 ∧ O * O.transpose = 1 ∧
      let Q : Matrix (Fin 3) (Fin 3) ℂ := fun i j => O i j
      N = Q * Matrix.diagonal lam * Q.transpose := by
  obtain ⟨hR, hS, hRS⟩ := in767_whole_conditional_normal_symmetric_parts_commute_three N hsym hnormal
  obtain ⟨O, r, s, horth, hcoorth, hr, hi⟩ := hdiag _ _ hR hS hRS
  refine ⟨O, fun k => (r k : ℂ) + Complex.I * (s k : ℂ), horth, hcoorth, ?_⟩
  dsimp only
  ext i j
  have hr' := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M i j) hr
  have hi' := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M i j) hi
  rw [Matrix.mul_apply] at hr' hi'
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_three] at hr' hi'
  rw [Matrix.mul_apply]
  apply Complex.ext <;>
    simp [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_three,
      Complex.mul_re, Complex.mul_im] <;> linarith

theorem qutrit_rank_four_block_product_from_three_lemmas
    (B : Matrix (Fin 3) (Fin 3) ℂ) (u : Fin 3 → ℂ)
    (hB : B.transpose = B)
    (hC : ∀ i j, star ((Bᴴ * B + vecMulVec u (star u)) i j) =
      (Bᴴ * B + vecMulVec u (star u)) i j)
    (hphase : ∀ (R S : Matrix (Fin 3) (Fin 3) ℝ) (x y : Fin 3 → ℝ),
      LinearIndependent ℝ ![x, y] →
      ∃ c s a b : ℝ, c*c + s*s = 1 ∧
        ∀ i : Fin 3, (R.mulVec (fun j => s*x j + c*y j)) i -
          (S.mulVec (fun j => c*x j - s*y j)) i +
            b*(c*x i - s*y i) - a*(s*x i + c*y i) = 0)
    (hdiag : ∀ (n : ℕ) (R S : Matrix (Fin n) (Fin n) ℝ),
      R.transpose = R → S.transpose = S → R*S = S*R →
      ∃ (O : Matrix (Fin n) (Fin n) ℝ) (r s : Fin n → ℝ),
        O.transpose * O = 1 ∧ O * O.transpose = 1 ∧
        R = O * Matrix.diagonal r * O.transpose ∧
        S = O * Matrix.diagonal s * O.transpose)
    (hfixed : ∀ (B : Matrix (Fin 3) (Fin 3) ℂ) (u : Fin 3 → ℂ)
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
          ∑ t, (b t * star (b t)) • vecMulVec (v t) (star (v t))) :
    ∃ (v : Fin 4 → Fin 3 → ℂ) (a b : Fin 4 → ℂ),
      (∀ t i, star (v t i) = v t i) ∧
      (1 : Matrix (Fin 3) (Fin 3) ℂ) =
        ∑ t, (a t * star (a t)) • vecMulVec (v t) (star (v t)) ∧
      B = ∑ t, (a t * star (b t)) • vecMulVec (v t) (star (v t)) ∧
      Bᴴ * B + vecMulVec u (star u) =
        ∑ t, (b t * star (b t)) • vecMulVec (v t) (star (v t)) := by
  by_cases hli : LinearIndependent ℝ ![(fun i : Fin 3 => (star (u i)).re),
                                        (fun i : Fin 3 => (star (u i)).im)]
  · exact in767_whole_conditional_rank_four_nondegenerate_from_phase_and_spectrum B u hB hC hli hphase (hdiag 4)
  · obtain ⟨v0, gamma, hu⟩ := in767_whole_conditional_dependent_re_im_fixed_phase u hli
    have hnorm : Bᴴ * B = B * Bᴴ := in767_whole_conditional_fixed_phase_block_normal B u v0 gamma hB hu hC
    obtain ⟨O, lam, ho, hoc, hspec⟩ :=
      in767_whole_conditional_normal_symmetric_spectral_of_real_pair_three B hB hnorm (hdiag 3)
    apply hfixed B u O lam v0 gamma ho hoc
    · intro i j
      have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M i j) hspec
      rw [Matrix.mul_apply] at h
      simpa only [Matrix.mul_diagonal, Matrix.transpose_apply] using h
    · exact hu
