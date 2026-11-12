import AFTD.Prelude

/-!
# qutrit_ppt_rank_four_bordered_normal_if_phase

Topic: quantum   Node: 991cc9309d80

Provenance: helper lemma. Helper for OP-693, based on the rank-four PPT source and the normal completion route in https://arxiv.org/abs/0903.0090.

The phase equation turns a symmetric qutrit block with a real rank-one Schur update into a normal complex symmetric bordered matrix.
-/

open Matrix
open scoped BigOperators Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
-- The normality of a symmetric bordered block reduces to its first row.
private lemma in767_bordered_normality
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

private lemma in767_bordered_h11
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

private lemma in767_bordered_h12
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

private lemma in767_bordered_completion
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
  apply in767_bordered_normality
  · exact in767_bordered_h11 B u ξ hB hC hξ
  · have h := in767_bordered_h12 R S x y a b hR hS hxy
    have hb : B = fun i j => (R i j : ℂ) + Complex.I * (S i j : ℂ) := by
      ext i j
      exact hRS i j
    have hw : (fun (i : Fin 3) (_ : Fin 1) => ξ * star (u i)) =
        (fun (i : Fin 3) (_ : Fin 1) => (x i : ℂ) + Complex.I * (y i : ℂ)) := by
      funext i j
      exact huw i
    simpa only [hb, hw] using h

theorem qutrit_ppt_rank_four_bordered_normal_if_phase
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
  exact in767_bordered_completion B u _ R S x y a b hB hRS hR hS hC hξ huw hphase
