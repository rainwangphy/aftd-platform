import AFTD.Prelude

/-!
# four_symmetric_normal_spectral_from_real_pair

Topic: quantum   Node: 3d0852b4b67b

Provenance: helper lemma. Helper for OP-693, in the rank-four normal-completion route related to https://arxiv.org/abs/0903.0090.

Complex symmetric normal four-by-four matrices have a real orthogonal eigenbasis, conditional on simultaneous diagonalization of commuting real symmetric four-by-four matrices.
-/

open Matrix
open scoped BigOperators Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
private lemma in767_spectralproof_normal_symmetric_parts_commute
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

theorem four_symmetric_normal_spectral_from_real_pair
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
  obtain ⟨hR, hS, hRS⟩ := in767_spectralproof_normal_symmetric_parts_commute N hsym hnormal
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
