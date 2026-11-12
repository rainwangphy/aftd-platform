import AFTD.Prelude
import AFTD.Kb.Tcs.PptQutritSteeredEffect
import AFTD.Kb.Tcs.OpenProblem693ThreeDimFewerThanNineIfLemmas
import AFTD.Kb.Tcs.PptQutritSourceProjectionBasisFromIsometryFactor
import AFTD.Kb.Tcs.RankTwoQutritProjectionIsometry
import AFTD.Kb.Tcs.PptQutritSourceNormalizedGramIfThreeLemmas
import AFTD.Kb.Tcs.PptQutritBellStatePartialTransposeInvariant
import AFTD.Kb.Tcs.RealPositiveQutritGramNormalizer
import AFTD.Kb.Tcs.PptQutritBellAliceBinaryEffectsValid
import AFTD.Kb.Tcs.PptQutritSteeredNormalizerMarginalIdentity
import AFTD.Kb.Tcs.ThreeOrthonormalRowsCodimensionOne
import AFTD.Kb.Tcs.RankFourPptNormalCompletionPhase
import AFTD.Kb.Tcs.RealSymmetricCommutingPairOrthogonalDiagonalization
import AFTD.Kb.Tcs.QutritFixedPhaseSchurFourProductDecomposition
import AFTD.Kb.Tcs.FiniteWeightedThreeBinaryHiddenModelHasParent
import AFTD.Kb.Tcs.PptQutritSteeredEffectIsValid
import AFTD.Kb.Tcs.RankOneQutritCompressionThreeBinaryParent
import AFTD.Kb.Tcs.PptQutritBellSetting
import AFTD.Kb.Tcs.PptQutritBellState
import AFTD.Kb.Tcs.PptQutritBellVector
import AFTD.Kb.Tcs.PptQutritSteeredNormalizer
import AFTD.Kb.Tcs.PptQutritSteeredUnnormalizedEffect
import AFTD.Kb.Tcs.V
import AFTD.Kb.Tcs.F

/-!
# ppt_qutrit_steered_effect_all_proper_subspaces_compatible

Topic: quantum   Node: 5e9d78332f62

Provenance: helper lemma. Helper for OP-693; the PPT compression argument in arXiv:2010.04048 Appendix A applied to the binary settings and PPT state of arXiv:1405.4502.

Every proper subspace compression of the three normalized steered effects has a joint parent.
-/

open Matrix
open scoped BigOperators Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
-- The normality of a symmetric bordered block reduces to its first row.
private lemma in770_rk2_bordered_normality
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

private lemma in770_rk2_bordered_h11
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

private lemma in770_rk2_bordered_h12
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

private lemma in770_rk2_bordered_completion
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
  apply in770_rk2_bordered_normality
  · exact in770_rk2_bordered_h11 B u ξ hB hC hξ
  · have h := in770_rk2_bordered_h12 R S x y a b hR hS hxy
    have hb : B = fun i j => (R i j : ℂ) + Complex.I * (S i j : ℂ) := by
      ext i j
      exact hRS i j
    have hw : (fun (i : Fin 3) (_ : Fin 1) => ξ * star (u i)) =
        (fun (i : Fin 3) (_ : Fin 1) => (x i : ℂ) + Complex.I * (y i : ℂ)) := by
      funext i j
      exact huw i
    simpa only [hb, hw] using h


private lemma in770_rk2_bordered_phase_completion
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
  exact in770_rk2_bordered_completion B u _ R S x y a b hB hRS hR hS hC hξ huw hphase

private lemma in770_rk2_bordered_lower_block
    (B : Matrix (Fin 3) (Fin 3) ℂ) (u : Fin 3 → ℂ) (ξ : ℂ)
    (hB : B.transpose = B)
    (hC : ∀ i j, star ((Bᴴ * B + vecMulVec u (star u)) i j) =
      (Bᴴ * B + vecMulVec u (star u)) i j)
    (hξ : ξ * star ξ = 1) :
    let W : Matrix (Fin 3) (Fin 1) ℂ := fun i _ => ξ * star (u i)
    Bᴴ * B + vecMulVec u (star u) = B * Bᴴ + W * Wᴴ := by
  dsimp only
  have h := in770_rk2_bordered_h11 B u ξ hB hC hξ
  dsimp only at h
  have hW : ((fun (i : Fin 3) (_ : Fin 1) => ξ * star (u i))ᵀᴴ *
      (fun (i : Fin 3) (_ : Fin 1) => ξ * star (u i))ᵀ) = vecMulVec u (star u) := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply,
      Matrix.vecMulVec_apply, Pi.star_apply, Fin.sum_univ_one, star_mul, star_star]
    linear_combination (u i * star (u j)) * hξ
  rw [hW] at h
  exact h


private lemma in770_rk2_product_frame_of_diagonal
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


private lemma in770_rk2_real_diagonal_normal_square
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


private lemma in770_rk2_spectral_frame_bridge
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
    exact in770_rk2_real_diagonal_normal_square Q lam hQreal hQorth
  have hm (f : Fin 4 → ℂ) (i j : Fin 3 ⊕ Fin 1) :
      (Q * Matrix.diagonal f * Q.transpose) i j =
        ∑ k, (O i k : ℂ) * f k * (O j k : ℂ) := by
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Q]
  apply in770_rk2_product_frame_of_diagonal B C V lam hV
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


private lemma in770_rk2_four_products_of_bordered_spectrum
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
  apply in770_rk2_spectral_frame_bridge B (Bᴴ * B + vecMulVec u (star u)) W Z O lam horth hcoorth
  · exact in770_rk2_bordered_lower_block B u ξ hB hC hξ
  · exact hN


private lemma in770_rk2_normal_symmetric_parts_commute
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

private lemma in770_rk2_normal_symmetric_spectral_of_real_pair
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
  obtain ⟨hR, hS, hRS⟩ := in770_rk2_normal_symmetric_parts_commute N hsym hnormal
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

private lemma in770_rk2_normal_spectrum_sum_index
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
    in770_rk2_normal_symmetric_spectral_of_real_pair N4 hs4 hn4 hdiag
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


private lemma in770_rk2_rank_four_nondegenerate_from_phase_and_spectrum
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
    exact in770_rk2_bordered_phase_completion B u c s a b hB hC hunit hxy
  have hz : Z.transpose = Z := by
    ext i j
    fin_cases i
    fin_cases j
    rfl
  have hs : N.transpose = N := by
    dsimp [N]
    rw [Matrix.fromBlocks_transpose, hB, Matrix.transpose_transpose, hz]
  obtain ⟨O, lam, ho, hoc, hspec⟩ := in770_rk2_normal_spectrum_sum_index N hs hn hdiag
  have hξ : ξ * star ξ = 1 := by
    dsimp [ξ]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> linarith
  exact in770_rk2_four_products_of_bordered_spectrum B u ξ Z O lam hB hC hξ ho hoc hspec


private lemma in770_rk2_dependent_re_im_fixed_phase (u : Fin 3 → ℂ)
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

private lemma in770_rk2_fixed_phase_block_normal
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


private lemma in770_rk2_normal_symmetric_parts_commute_three
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

private lemma in770_rk2_normal_symmetric_spectral_of_real_pair_three
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
  obtain ⟨hR, hS, hRS⟩ := in770_rk2_normal_symmetric_parts_commute_three N hsym hnormal
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


private lemma in770_rk2_rank_four_from_phase_spectrum_and_fixed
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
  · exact in770_rk2_rank_four_nondegenerate_from_phase_and_spectrum B u hB hC hli hphase (hdiag 4)
  · obtain ⟨v0, gamma, hu⟩ := in770_rk2_dependent_re_im_fixed_phase u hli
    have hnorm : Bᴴ * B = B * Bᴴ := in770_rk2_fixed_phase_block_normal B u v0 gamma hB hu hC
    obtain ⟨O, lam, ho, hoc, hspec⟩ :=
      in770_rk2_normal_symmetric_spectral_of_real_pair_three B hB hnorm (hdiag 3)
    apply hfixed B u O lam v0 gamma ho hoc
    · intro i j
      have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M i j) hspec
      rw [Matrix.mul_apply] at h
      simpa only [Matrix.mul_diagonal, Matrix.transpose_apply] using h
    · exact hu


private lemma in770_rk2_gram_schur_rank_one
    (U V : Matrix (Fin 3) (Fin 4) ℂ) (w : Fin 4 → ℂ)
    (hcomp : 1 - Uᴴ * U = vecMulVec w (star w)) :
    let B := U * Vᴴ
    let u := V *ᵥ w
    V * Vᴴ = Bᴴ * B + vecMulVec u (star u) := by
  dsimp only
  have hw : V * vecMulVec w (star w) * Vᴴ = vecMulVec (V *ᵥ w) (star (V *ᵥ w)) := by
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec]
  calc
    V * Vᴴ = V * ((1 - Uᴴ * U) + Uᴴ * U) * Vᴴ := by simp
    _ = V * (Uᴴ * U) * Vᴴ + V * (1 - Uᴴ * U) * Vᴴ := by
      rw [Matrix.mul_add, Matrix.add_mul, add_comm]
    _ = (U * Vᴴ)ᴴ * (U * Vᴴ) + vecMulVec (V *ᵥ w) (star (V *ᵥ w)) := by
      rw [hcomp, hw, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      simp only [Matrix.mul_assoc]


private lemma in770_rk2_block_products_to_bipartite
    (B C : Matrix (Fin 3) (Fin 3) ℂ)
    (v : Fin 4 → Fin 3 → ℂ) (a b : Fin 4 → ℂ)
    (hv : ∀ t i, star (v t i) = v t i)
    (h0 : (1 : Matrix (Fin 3) (Fin 3) ℂ) =
      ∑ t, (a t * star (a t)) • vecMulVec (v t) (star (v t)))
    (hB : B = ∑ t, (a t * star (b t)) • vecMulVec (v t) (star (v t)))
    (hC : C = ∑ t, (b t * star (b t)) • vecMulVec (v t) (star (v t))) :
    ∀ (i j : Fin 3) (p q : Fin 2),
      (if p = 0 then if q = 0 then (1 : Matrix (Fin 3) (Fin 3) ℂ) i j else B i j
       else if q = 0 then Bᴴ i j else C i j) =
      ∑ t, (v t i * ![a t, b t] p) * star (v t j * ![a t, b t] q) := by
  intro i j p q
  have h0' := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M i j) h0
  have hB' := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M i j) hB
  have hC' := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M i j) hC
  have hBt := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M j i) hB
  fin_cases p <;> fin_cases q
  · simpa [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, hv,
      smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using h0'
  · simpa [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, hv,
      smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hB'
  · have hBt' := congrArg star hBt
    simpa [Matrix.conjTranspose_apply, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.vecMulVec_apply, star_sum, hv, smul_eq_mul,
      mul_comm, mul_left_comm, mul_assoc] using hBt'
  · simpa [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, hv,
      smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hC'


private lemma in770_rk2_pt_hermitian_blocks
    (X : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ) (hX : X.IsHermitian)
    (hpt : ∀ i j : Fin 3, ∀ p q : Fin 2, X (i,p) (j,q) = X (j,p) (i,q)) :
    (let B : Matrix (Fin 3) (Fin 3) ℂ := fun i j => X (i,0) (j,1); B.transpose = B) ∧
    (∀ i j : Fin 3, ∀ p : Fin 2, star (X (i,p) (j,p)) = X (i,p) (j,p)) := by
  constructor
  · ext i j
    exact hpt j i 0 1
  · intro i j p
    calc
      star (X (i,p) (j,p)) = X (j,p) (i,p) := hX.apply (j,p) (i,p)
      _ = X (i,p) (j,p) := hpt j i p p


private lemma in770_rk2_normalized_gram_four_products
    (F : Matrix (Fin 3 × Fin 2) (Fin 4) ℂ)
    (hupper : (let U : Matrix (Fin 3) (Fin 4) ℂ := fun i t => F (i,0) t; U*Uᴴ = 1))
    (hpt : ∀ i j : Fin 3, ∀ p q : Fin 2, (F*Fᴴ) (i,p) (j,q) = (F*Fᴴ) (j,p) (i,q))
    (hcodim : ∀ U : Matrix (Fin 3) (Fin 4) ℂ, U*Uᴴ = 1 →
      ∃ w : Fin 4 → ℂ, 1 - Uᴴ*U = vecMulVec w (star w))
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
    ∃ (v : Fin 4 → Fin 3 → ℂ) (z : Fin 4 → Fin 2 → ℂ),
      ∀ (i j : Fin 3) (p q : Fin 2),
        (F*Fᴴ) (i,p) (j,q) = ∑ t, (v t i * z t p) * star (v t j * z t q) := by
  let U : Matrix (Fin 3) (Fin 4) ℂ := fun i t => F (i,0) t
  let V : Matrix (Fin 3) (Fin 4) ℂ := fun i t => F (i,1) t
  let B : Matrix (Fin 3) (Fin 3) ℂ := U*Vᴴ
  let C : Matrix (Fin 3) (Fin 3) ℂ := V*Vᴴ
  let X : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ := F*Fᴴ
  have hX : X.IsHermitian := Matrix.isHermitian_mul_conjTranspose_self F
  obtain ⟨hB, hreal⟩ := in770_rk2_pt_hermitian_blocks X hX hpt
  have hB' : B.transpose = B := by
    ext i j
    have hh := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M i j) hB
    simpa [B, U, V, X, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply] using hh
  have hC : ∀ i j, star (C i j) = C i j := by
    intro i j
    simpa [C, V, X, Matrix.mul_apply, Matrix.conjTranspose_apply] using hreal i j 1
  obtain ⟨w, hw⟩ := hcodim U hupper
  let u := V *ᵥ w
  have hschur : C = Bᴴ*B + vecMulVec u (star u) := in770_rk2_gram_schur_rank_one U V w hw
  have hC' : ∀ i j, star ((Bᴴ * B + vecMulVec u (star u)) i j) =
      (Bᴴ * B + vecMulVec u (star u)) i j := by
    rw [← hschur]
    exact hC
  obtain ⟨v, a, b, hv, h0, hb, hc⟩ :=
    in770_rk2_rank_four_from_phase_spectrum_and_fixed B u hB' hC' hphase hdiag hfixed
  have hc' : C = ∑ t, (b t * star (b t)) • vecMulVec (v t) (star (v t)) := hschur.trans hc
  refine ⟨v, fun t => ![a t, b t], ?_⟩
  intro i j p q
  have hh := in770_rk2_block_products_to_bipartite B C v a b hv h0 hb hc' i j p q
  have heq : X (i,p) (j,q) =
      (if p = 0 then if q = 0 then (1 : Matrix (Fin 3) (Fin 3) ℂ) i j else B i j
       else if q = 0 then Bᴴ i j else C i j) := by
    fin_cases p <;> fin_cases q
    · simpa [X, U, Matrix.mul_apply, Matrix.conjTranspose_apply] using congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M i j) hupper
    · simp [X, B, U, V, Matrix.mul_apply, Matrix.conjTranspose_apply]
    · simp [X, B, U, V, Matrix.mul_apply, Matrix.conjTranspose_apply, star_sum, star_mul, mul_comm]
    · simp [X, C, V, Matrix.mul_apply, Matrix.conjTranspose_apply]
  exact heq.trans hh


private lemma in770_rk2_bipartite_product_congruence
    (T : Matrix (Fin 3) (Fin 3) ℂ) (v : Fin 4 → Fin 3 → ℂ) (z : Fin 4 → Fin 2 → ℂ)
    (i j : Fin 3) (p q : Fin 2) :
    (∑ a : Fin 3, ∑ b : Fin 3, T i a *
      (∑ t : Fin 4, (v t a * z t p) * star (v t b * z t q)) * star (T j b)) =
      ∑ t : Fin 4, ((T *ᵥ v t) i * z t p) * star ((T *ᵥ v t) j * z t q) := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_four, star_mul, star_sum]
  ring


private lemma in770_rk2_four_column_gram_congruence
    (T : Matrix (Fin 3) (Fin 3) ℂ) (F : Matrix (Fin 3 × Fin 2) (Fin 4) ℂ)
    (i j : Fin 3) (p q : Fin 2) :
    (∑ t : Fin 4, (∑ a : Fin 3, T i a * F (a,p) t) *
      star (∑ b : Fin 3, T j b * F (b,q) t)) =
      ∑ a : Fin 3, ∑ b : Fin 3, T i a * (F*Fᴴ) (a,p) (b,q) * star (T j b) := by
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_three, Fin.sum_univ_four, star_mul]
  ring


private lemma in770_rk2_unfiltered_gram_four_products
    (F : Matrix (Fin 3 × Fin 2) (Fin 4) ℂ) (T : Matrix (Fin 3) (Fin 3) ℂ)
    (hupper : (let U : Matrix (Fin 3) (Fin 4) ℂ := fun i t => F (i,0) t; U*Uᴴ = 1))
    (hpt : ∀ i j : Fin 3, ∀ p q : Fin 2, (F*Fᴴ) (i,p) (j,q) = (F*Fᴴ) (j,p) (i,q))
    (hcodim : ∀ U : Matrix (Fin 3) (Fin 4) ℂ, U*Uᴴ = 1 →
      ∃ w : Fin 4 → ℂ, 1 - Uᴴ*U = vecMulVec w (star w))
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
    ∃ (v : Fin 4 → Fin 3 → ℂ) (z : Fin 4 → Fin 2 → ℂ),
      ∀ (i j : Fin 3) (p q : Fin 2),
        (∑ t : Fin 4, (∑ a : Fin 3, T i a * F (a,p) t) *
          star (∑ b : Fin 3, T j b * F (b,q) t)) =
        ∑ t, (v t i * z t p) * star (v t j * z t q) := by
  obtain ⟨v, z, hvz⟩ := in770_rk2_normalized_gram_four_products F hupper hpt hcodim hphase hdiag hfixed
  refine ⟨fun t => T *ᵥ v t, z, ?_⟩
  intro i j p q
  rw [in770_rk2_four_column_gram_congruence]
  simp_rw [hvz]
  exact in770_rk2_bipartite_product_congruence T v z i j p q


private lemma in770_rk2_product_assemblage_parent_of_weighted
    (n m : ℕ) (A : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ)
    (v : Fin m → Fin 3 → ℂ) (w : Fin m → Fin n → ℂ)
    (hA : ∀ j, (A j).PosSemidef ∧ (1-A j).PosSemidef)
    (hweighted : ∀ (Q : Fin m → Matrix (Fin n) (Fin n) ℂ)
      (r : Fin m → ℝ) (p : Fin 3 → Fin m → ℝ) (P : Matrix (Fin n) (Fin n) ℂ),
      (∀ t, (Q t).PosSemidef) → (∑ t, (r t) • Q t) = P →
      (∀ t, 0 ≤ r t) → (∀ j t, 0 ≤ p j t ∧ p j t ≤ r t) →
      ∃ G : (Fin 3 → Bool) → Matrix (Fin n) (Fin n) ℂ,
        (∀ s, (G s).PosSemidef) ∧ (∑ s, G s) = P ∧
        ∀ j : Fin 3, (∑ s, if s j then G s else 0) = ∑ t, (p j t) • Q t) :
    ∃ G : (Fin 3 → Bool) → Matrix (Fin n) (Fin n) ℂ,
      (∀ s, (G s).PosSemidef) ∧
      (∑ s, G s) = ∑ t, (star (v t) ⬝ᵥ v t).re • vecMulVec (w t) (star (w t)) ∧
      ∀ j : Fin 3, (∑ s, if s j then G s else 0) =
        ∑ t, (star (v t) ⬝ᵥ ((A j) *ᵥ v t)).re • vecMulVec (w t) (star (w t)) := by
  apply hweighted (fun t => vecMulVec (w t) (star (w t)))
    (fun t => (star (v t) ⬝ᵥ v t).re)
    (fun j t => (star (v t) ⬝ᵥ ((A j) *ᵥ v t)).re)
    (∑ t, (star (v t) ⬝ᵥ v t).re • vecMulVec (w t) (star (w t)))
  · intro t
    exact Matrix.posSemidef_vecMulVec_self_star _
  · rfl
  · intro t
    have h := (Matrix.PosSemidef.one : (1 : Matrix (Fin 3) (Fin 3) ℂ).PosSemidef).dotProduct_mulVec_nonneg (v t)
    have hr := (Complex.nonneg_iff.mp h).1
    simpa using hr
  · intro j t
    have hlo := (Complex.nonneg_iff.mp ((hA j).1.dotProduct_mulVec_nonneg (v t))).1
    have hhi := (Complex.nonneg_iff.mp ((hA j).2.dotProduct_mulVec_nonneg (v t))).1
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, Complex.sub_re] at hhi
    exact ⟨hlo, by linarith⟩


private lemma in770_rk2_steer_four_products
    {n : ℕ} (A : Matrix (Fin 3) (Fin 3) ℂ)
    (v : Fin 4 → Fin 3 → ℂ) (w : Fin 4 → Fin n → ℂ) (x y : Fin n) :
    (∑ i : Fin 3, ∑ j : Fin 3,
      (∑ t : Fin 4, (v t i * w t x) * star (v t j * w t y)) * A j i) =
      ∑ t : Fin 4, (star (v t) ⬝ᵥ (A *ᵥ v t)) * (w t x * star (w t y)) := by
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three, Fin.sum_univ_four,
    star_mul]
  ring

private lemma in770_rk2_marginal_four_products
    {n : ℕ} (v : Fin 4 → Fin 3 → ℂ) (w : Fin 4 → Fin n → ℂ) (x y : Fin n) :
    (∑ i : Fin 3, ∑ t : Fin 4, (v t i * w t x) * star (v t i * w t y)) =
      ∑ t : Fin 4, (star (v t) ⬝ᵥ v t) * (w t x * star (w t y)) := by
  simp [dotProduct, Fin.sum_univ_three, Fin.sum_univ_four, star_mul]
  ring


private lemma in770_rk2_separable_steering_parent_of_weighted
    (n : ℕ) (A : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ)
    (v : Fin 4 → Fin 3 → ℂ) (w : Fin 4 → Fin n → ℂ)
    (hA : ∀ j, (A j).PosSemidef ∧ (1-A j).PosSemidef)
    (hweighted : ∀ (Q : Fin 4 → Matrix (Fin n) (Fin n) ℂ)
      (r : Fin 4 → ℝ) (p : Fin 3 → Fin 4 → ℝ) (P : Matrix (Fin n) (Fin n) ℂ),
      (∀ t, (Q t).PosSemidef) → (∑ t, (r t) • Q t) = P →
      (∀ t, 0 ≤ r t) → (∀ j t, 0 ≤ p j t ∧ p j t ≤ r t) →
      ∃ G : (Fin 3 → Bool) → Matrix (Fin n) (Fin n) ℂ,
        (∀ s, (G s).PosSemidef) ∧ (∑ s, G s) = P ∧
        ∀ j : Fin 3, (∑ s, if s j then G s else 0) = ∑ t, (p j t) • Q t) :
    ∃ G : (Fin 3 → Bool) → Matrix (Fin n) (Fin n) ℂ,
      (∀ s, (G s).PosSemidef) ∧
      (∑ s, G s) = (fun x y => ∑ i : Fin 3, ∑ t : Fin 4,
        (v t i * w t x) * star (v t i * w t y)) ∧
      ∀ j : Fin 3, (∑ s, if s j then G s else 0) =
        (fun x y => ∑ i : Fin 3, ∑ k : Fin 3,
          (∑ t : Fin 4, (v t i * w t x) * star (v t k * w t y)) * A j k i) := by
  obtain ⟨G, hG, hsum, hmarg⟩ := in770_rk2_product_assemblage_parent_of_weighted n 4 A v w hA hweighted
  refine ⟨G, hG, ?_, ?_⟩
  · rw [hsum]
    ext x y
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply,
      smul_eq_mul]
    rw [in770_rk2_marginal_four_products]
    apply Finset.sum_congr rfl
    intro t ht
    have hn := (Complex.nonneg_iff.mp ((Matrix.PosSemidef.one :
      (1 : Matrix (Fin 3) (Fin 3) ℂ).PosSemidef).dotProduct_mulVec_nonneg (v t))).2
    simp only [Matrix.one_mulVec] at hn
    have hr : (((star (v t) ⬝ᵥ v t).re : ℝ) : ℂ) = star (v t) ⬝ᵥ v t := by
      apply Complex.ext <;> simp [hn]
    rw [Complex.real_smul, hr]
  · intro j
    rw [hmarg j]
    ext x y
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply,
      smul_eq_mul]
    rw [in770_rk2_steer_four_products]
    apply Finset.sum_congr rfl
    intro t ht
    have hn := (Complex.nonneg_iff.mp ((hA j).1.dotProduct_mulVec_nonneg (v t))).2
    have hr : (((star (v t) ⬝ᵥ (A j *ᵥ v t)).re : ℝ) : ℂ) =
        star (v t) ⬝ᵥ (A j *ᵥ v t) := by
      apply Complex.ext <;> simp [hn]
    rw [Complex.real_smul, hr]


private lemma in770_rk2_unfiltered_gram_steering_parent
    (F : Matrix (Fin 3 × Fin 2) (Fin 4) ℂ) (T : Matrix (Fin 3) (Fin 3) ℂ)
    (A : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ)
    (hA : ∀ j, (A j).PosSemidef ∧ (1-A j).PosSemidef)
    (hupper : (let U : Matrix (Fin 3) (Fin 4) ℂ := fun i t => F (i,0) t; U*Uᴴ = 1))
    (hpt : ∀ i j : Fin 3, ∀ p q : Fin 2, (F*Fᴴ) (i,p) (j,q) = (F*Fᴴ) (j,p) (i,q))
    (hcodim : ∀ U : Matrix (Fin 3) (Fin 4) ℂ, U*Uᴴ = 1 →
      ∃ w : Fin 4 → ℂ, 1 - Uᴴ*U = vecMulVec w (star w))
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
          ∑ t, (b t * star (b t)) • vecMulVec (v t) (star (v t)))
    (hweighted : ∀ (Q : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ)
      (r : Fin 4 → ℝ) (p : Fin 3 → Fin 4 → ℝ) (P : Matrix (Fin 2) (Fin 2) ℂ),
      (∀ t, (Q t).PosSemidef) → (∑ t, (r t) • Q t) = P →
      (∀ t, 0 ≤ r t) → (∀ j t, 0 ≤ p j t ∧ p j t ≤ r t) →
      ∃ G : (Fin 3 → Bool) → Matrix (Fin 2) (Fin 2) ℂ,
        (∀ s, (G s).PosSemidef) ∧ (∑ s, G s) = P ∧
        ∀ j : Fin 3, (∑ s, if s j then G s else 0) = ∑ t, (p j t) • Q t) :
    ∃ G : (Fin 3 → Bool) → Matrix (Fin 2) (Fin 2) ℂ,
      (∀ s, (G s).PosSemidef) ∧
      (∑ s, G s) = (fun p q => ∑ i : Fin 3, (∑ t : Fin 4, (∑ a : Fin 3, T i a * F (a,p) t) *
        star (∑ b : Fin 3, T i b * F (b,q) t))) ∧
      ∀ j : Fin 3, (∑ s, if s j then G s else 0) =
        (fun p q => ∑ i : Fin 3, ∑ k : Fin 3, (∑ t : Fin 4, (∑ a : Fin 3, T i a * F (a,p) t) *
            star (∑ b : Fin 3, T k b * F (b,q) t)) * A j k i) := by
  obtain ⟨v, z, hvz⟩ := in770_rk2_unfiltered_gram_four_products F T hupper hpt hcodim hphase hdiag hfixed
  obtain ⟨G, hG, hsum, hmarg⟩ := in770_rk2_separable_steering_parent_of_weighted 2 A v z hA hweighted
  refine ⟨G, hG, ?_, ?_⟩
  · rw [hsum]
    ext p q
    apply Finset.sum_congr rfl
    intro i hi
    exact (hvz i i p q).symm
  · intro j
    rw [hmarg j]
    ext p q
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro k hk
    rw [hvz i k p q]


private lemma in770_rk2_compressed_rankfour_gram
    (v : Fin 4 → Fin 3 × Fin 3 → ℂ) (lam : Fin 4 → ℝ)
    (W : Matrix (Fin 3) (Fin 2) ℂ) (hlam : ∀ t, 0 ≤ lam t)
    (i j : Fin 3) (p q : Fin 2) :
    (∑ x : Fin 3, ∑ y : Fin 3, star (W x p) *
      (∑ t : Fin 4, (lam t : ℂ) * v t (i,x) * star (v t (j,y))) * W y q) =
    ∑ t : Fin 4,
      ((Real.sqrt (lam t) : ℂ) * ∑ x : Fin 3, star (W x p) * v t (i,x)) *
      star ((Real.sqrt (lam t) : ℂ) * ∑ y : Fin 3, star (W y q) * v t (j,y)) := by
  have hsq (t : Fin 4) : (Real.sqrt (lam t) : ℂ)^2 = (lam t : ℂ) := by
    exact_mod_cast Real.sq_sqrt (hlam t)
  simp [Fin.sum_univ_three, Fin.sum_univ_four, star_mul, star_add]
  ring_nf
  simp only [hsq]
  ring


private lemma in770_rk2_steering_commutes_with_second_filter
    (ρ : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ)
    (A : Matrix (Fin 3) (Fin 3) ℂ) (W : Matrix (Fin 3) (Fin 2) ℂ)
    (p q : Fin 2) :
    (∑ i : Fin 3, ∑ j : Fin 3,
      (∑ x : Fin 3, ∑ y : Fin 3, star (W x p) * ρ (i,x) (j,y) * W y q) * A j i) =
    ∑ x : Fin 3, ∑ y : Fin 3, star (W x p) *
      (∑ i : Fin 3, ∑ j : Fin 3, ρ (i,x) (j,y) * A j i) * W y q := by
  simp [Fin.sum_univ_three]
  ring


private lemma in770_rk2_compressed_source_parent
    (F : Matrix (Fin 3 × Fin 2) (Fin 4) ℂ) (T : Matrix (Fin 3) (Fin 3) ℂ)
    (source : Fin 4 → Fin 3 × Fin 3 → ℂ) (lam : Fin 4 → ℝ)
    (W : Matrix (Fin 3) (Fin 2) ℂ) (A : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ)
    (hlam : ∀ t, 0 ≤ lam t)
    (hrel : ∀ i : Fin 3, ∀ p : Fin 2, ∀ t : Fin 4,
      (Real.sqrt (lam t) : ℂ) * (∑ x : Fin 3, star (W x p) * source t (i,x)) =
        ∑ a : Fin 3, T i a * F (a,p) t)
    (hA : ∀ j, (A j).PosSemidef ∧ (1-A j).PosSemidef)
    (hupper : (let U : Matrix (Fin 3) (Fin 4) ℂ := fun i t => F (i,0) t; U*Uᴴ = 1))
    (hpt : ∀ i j : Fin 3, ∀ p q : Fin 2, (F*Fᴴ) (i,p) (j,q) = (F*Fᴴ) (j,p) (i,q))
    (hcodim : ∀ U : Matrix (Fin 3) (Fin 4) ℂ, U*Uᴴ = 1 →
      ∃ w : Fin 4 → ℂ, 1 - Uᴴ*U = vecMulVec w (star w))
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
      (O : Matrix (Fin 3) (Fin 3) ℝ) (e : Fin 3 → ℂ)
      (v0 : Fin 3 → ℝ) (gamma : ℂ),
      O.transpose * O = 1 → O * O.transpose = 1 →
      (∀ i j, B i j = ∑ k, (O i k : ℂ) * e k * (O j k : ℂ)) →
      (∀ i, u i = gamma * (v0 i : ℂ)) →
      ∃ (v : Fin 4 → Fin 3 → ℂ) (a b : Fin 4 → ℂ),
        (∀ t i, star (v t i) = v t i) ∧
        (1 : Matrix (Fin 3) (Fin 3) ℂ) =
          ∑ t, (a t * star (a t)) • vecMulVec (v t) (star (v t)) ∧
        B = ∑ t, (a t * star (b t)) • vecMulVec (v t) (star (v t)) ∧
        Bᴴ * B + vecMulVec u (star u) =
          ∑ t, (b t * star (b t)) • vecMulVec (v t) (star (v t)))
    (hweighted : ∀ (Q : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ)
      (r : Fin 4 → ℝ) (p : Fin 3 → Fin 4 → ℝ) (P : Matrix (Fin 2) (Fin 2) ℂ),
      (∀ t, (Q t).PosSemidef) → (∑ t, (r t) • Q t) = P →
      (∀ t, 0 ≤ r t) → (∀ j t, 0 ≤ p j t ∧ p j t ≤ r t) →
      ∃ G : (Fin 3 → Bool) → Matrix (Fin 2) (Fin 2) ℂ,
        (∀ s, (G s).PosSemidef) ∧ (∑ s, G s) = P ∧
        ∀ j : Fin 3, (∑ s, if s j then G s else 0) = ∑ t, (p j t) • Q t) :
    let ρ : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ := fun ax cy =>
      ∑ t : Fin 4, (lam t : ℂ) * source t ax * star (source t cy)
    ∃ G : (Fin 3 → Bool) → Matrix (Fin 2) (Fin 2) ℂ,
      (∀ s, (G s).PosSemidef) ∧
      (∑ s, G s) = (fun p q => ∑ x : Fin 3, ∑ y : Fin 3,
        star (W x p) * (∑ i : Fin 3, ρ (i,x) (i,y)) * W y q) ∧
      ∀ j : Fin 3, (∑ s, if s j then G s else 0) =
        (fun p q => ∑ x : Fin 3, ∑ y : Fin 3, star (W x p) *
          (∑ i : Fin 3, ∑ k : Fin 3, ρ (i,x) (k,y) * A j k i) * W y q) := by
  dsimp only
  obtain ⟨G, hG, hsum, hmarg⟩ := in770_rk2_unfiltered_gram_steering_parent
    F T A hA hupper hpt hcodim hphase hdiag hfixed hweighted
  have hfactor (i j : Fin 3) (p q : Fin 2) :
      (∑ t : Fin 4, (∑ a : Fin 3, T i a * F (a,p) t) *
        star (∑ b : Fin 3, T j b * F (b,q) t)) =
      ∑ x : Fin 3, ∑ y : Fin 3, star (W x p) *
        (∑ t : Fin 4, (lam t : ℂ) * source t (i,x) * star (source t (j,y))) * W y q := by
    rw [in770_rk2_compressed_rankfour_gram source lam W hlam i j p q]
    apply Finset.sum_congr rfl
    intro t ht
    rw [hrel i p t, hrel j q t]
  refine ⟨G, hG, ?_, ?_⟩
  · rw [hsum]
    ext p q
    simp_rw [hfactor]
    simp [Fin.sum_univ_three]
    ring
  · intro j
    rw [hmarg j]
    ext p q
    simp_rw [hfactor]
    exact in770_rk2_steering_commutes_with_second_filter
      (fun ax cy => ∑ t : Fin 4, (lam t : ℂ) * source t ax * star (source t cy)) (A j) W p q


private lemma in770_rk2_lift_qubit_parent
    (M : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ) (U : Matrix (Fin 3) (Fin 2) ℂ)
    (G : (Fin 3 → Bool) → Matrix (Fin 2) (Fin 2) ℂ)
    (hG : ∀ s, (G s).PosSemidef) (hsum : (∑ s, G s) = 1)
    (hmarg : ∀ j, (∑ s, if s j then G s else 0) = Uᴴ * M j * U) :
    ∃ H : (Fin 3 → Bool) → Matrix (Fin 3) (Fin 3) ℂ,
      (∀ s, (H s).PosSemidef) ∧ (∑ s, H s) = U*Uᴴ ∧
      ∀ j : Fin 3, (∑ s, if s j then H s else 0) = (U*Uᴴ)*M j*(U*Uᴴ) := by
  let lift (X : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 3) (Fin 3) ℂ := U * X * Uᴴ
  have hzero : lift 0 = 0 := by
    ext i j
    simp [lift, Matrix.mul_apply]
  have hlin (f : (Fin 3 → Bool) → Matrix (Fin 2) (Fin 2) ℂ) :
      (∑ s, lift (f s)) = lift (∑ s, f s) := by
    ext i j
    simp only [Matrix.sum_apply]
    simp [lift, Matrix.mul_apply, Matrix.sum_apply, Fin.sum_univ_two,
      Finset.sum_mul, Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_comm, add_mul]
  refine ⟨fun s => lift (G s), ?_, ?_, ?_⟩
  · intro s
    exact (hG s).mul_mul_conjTranspose_same U
  · rw [hlin, hsum]
    simp [lift]
  · intro j
    have heq : (∑ s, if s j then lift (G s) else 0) =
        ∑ s, lift (if s j then G s else 0) := by
      apply Finset.sum_congr rfl
      intro s hs
      cases h : s j <;> simp [h, hzero]
    rw [heq, hlin, hmarg]
    dsimp [lift]
    rw [← Matrix.mul_assoc U (Uᴴ * M j) U, ← Matrix.mul_assoc U Uᴴ (M j)]
    exact Matrix.mul_assoc _ _ _


private lemma in770_rk2_normalizer_hermitian : ppt_qutrit_steered_normalizerᴴ = ppt_qutrit_steered_normalizer := by
  ext i j
  by_cases h : i = j
  · subst j
    by_cases hi : i = 2 <;> simp [ppt_qutrit_steered_normalizer, Matrix.conjTranspose_apply, Matrix.diagonal_apply, hi]
  · simp [ppt_qutrit_steered_normalizer, Matrix.conjTranspose_apply, Matrix.diagonal_apply, h, Ne.symm h]


private lemma in770_rk2_filter_matrix_entries
    (W : Matrix (Fin 3) (Fin 2) ℂ) (M : Matrix (Fin 3) (Fin 3) ℂ) (p q : Fin 2) :
    (∑ x : Fin 3, ∑ y : Fin 3, star (W x p) * M x y * W y q) = (Wᴴ*M*W) p q := by
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_three]
  ring


private def in770_rk2_source_alice_valid_statement : Prop :=
  ∀ j : Fin 3,
    let A : Matrix (Fin 3) (Fin 3) ℂ :=
      vecMulVec (ppt_qutrit_bell_setting j) (star (ppt_qutrit_bell_setting j))
    A.PosSemidef ∧ (1-A).PosSemidef

private def in770_rk2_source_normalized_gram_statement : Prop :=
  ∀ P : Matrix (Fin 3) (Fin 3) ℂ, P.IsHermitian → P*P=P → P.rank=2 →
    ∃ (U : Matrix (Fin 3) (Fin 2) ℂ) (F : Matrix (Fin 3 × Fin 2) (Fin 4) ℂ)
      (T : Matrix (Fin 3) (Fin 3) ℂ),
      Uᴴ*U=1 ∧ U*Uᴴ=P ∧
      (let V : Matrix (Fin 3) (Fin 4) ℂ := fun i t => F (i,0) t; V*Vᴴ=1) ∧
      (∀ i j : Fin 3, ∀ p q : Fin 2, (F*Fᴴ) (i,p) (j,q) = (F*Fᴴ) (j,p) (i,q)) ∧
      (let W : Matrix (Fin 3) (Fin 2) ℂ := ppt_qutrit_steered_normalizer * U
       let lam : Fin 4 → ℝ := fun t => if t = 0 then 3257/6884 else if t = 3 then 27/6884 else 450/1721
       ∀ i : Fin 3, ∀ p : Fin 2, ∀ t : Fin 4,
        (Real.sqrt (lam t) : ℂ) * (∑ x : Fin 3, star (W x p) * ppt_qutrit_bell_vector t (i,x)) =
          ∑ a : Fin 3, T i a * F (a,p) t)


private lemma in770_rk2_rank_two_source_compatibility_if_lemmas
    (hgram : in770_rk2_source_normalized_gram_statement)
    (halice : in770_rk2_source_alice_valid_statement)
    (hmarginal : (let M : Matrix (Fin 3) (Fin 3) ℂ := (fun x y => ∑ i : Fin 3, ppt_qutrit_bell_state (i,x) (i,y));
      ppt_qutrit_steered_normalizer * M * ppt_qutrit_steered_normalizer = 1))
    (hcodim : ∀ U : Matrix (Fin 3) (Fin 4) ℂ, U*Uᴴ = 1 →
      ∃ w : Fin 4 → ℂ, 1 - Uᴴ*U = vecMulVec w (star w))
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
      (O : Matrix (Fin 3) (Fin 3) ℝ) (e : Fin 3 → ℂ)
      (v0 : Fin 3 → ℝ) (gamma : ℂ),
      O.transpose * O = 1 → O * O.transpose = 1 →
      (∀ i j, B i j = ∑ k, (O i k : ℂ) * e k * (O j k : ℂ)) →
      (∀ i, u i = gamma * (v0 i : ℂ)) →
      ∃ (v : Fin 4 → Fin 3 → ℂ) (a b : Fin 4 → ℂ),
        (∀ t i, star (v t i) = v t i) ∧
        (1 : Matrix (Fin 3) (Fin 3) ℂ) =
          ∑ t, (a t * star (a t)) • vecMulVec (v t) (star (v t)) ∧
        B = ∑ t, (a t * star (b t)) • vecMulVec (v t) (star (v t)) ∧
        Bᴴ * B + vecMulVec u (star u) =
          ∑ t, (b t * star (b t)) • vecMulVec (v t) (star (v t)))
    (hweighted : ∀ (Q : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ)
      (r : Fin 4 → ℝ) (p : Fin 3 → Fin 4 → ℝ) (P : Matrix (Fin 2) (Fin 2) ℂ),
      (∀ t, (Q t).PosSemidef) → (∑ t, (r t) • Q t) = P →
      (∀ t, 0 ≤ r t) → (∀ j t, 0 ≤ p j t ∧ p j t ≤ r t) →
      ∃ G : (Fin 3 → Bool) → Matrix (Fin 2) (Fin 2) ℂ,
        (∀ s, (G s).PosSemidef) ∧ (∑ s, G s) = P ∧
        ∀ j : Fin 3, (∑ s, if s j then G s else 0) = ∑ t, (p j t) • Q t) :
    ∀ P : Matrix (Fin 3) (Fin 3) ℂ, P.IsHermitian → P*P=P → P.rank=2 →
      ∃ G : (Fin 3 → Bool) → Matrix (Fin 3) (Fin 3) ℂ,
        (∀ s, (G s).PosSemidef) ∧ (∑ s, G s) = P ∧
        ∀ j : Fin 3, (∑ s, if s j then G s else 0) = P*ppt_qutrit_steered_effect j*P := by
  intro P hP hPP hRank
  obtain ⟨U, F, T, hU, hUP, hupper, hpt, hrel⟩ := hgram P hP hPP hRank
  let N := ppt_qutrit_steered_normalizer
  let W : Matrix (Fin 3) (Fin 2) ℂ := N*U
  let A : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ := fun j =>
    vecMulVec (ppt_qutrit_bell_setting j) (star (ppt_qutrit_bell_setting j))
  let lam : Fin 4 → ℝ := fun t => if t = 0 then 3257/6884 else if t = 3 then 27/6884 else 450/1721
  have hlam : ∀ t, 0 ≤ lam t := by intro t; dsimp [lam]; split_ifs <;> norm_num
  obtain ⟨G, hG, hsum, hmeas⟩ := in770_rk2_compressed_source_parent F T
    ppt_qutrit_bell_vector lam W A hlam hrel halice hupper hpt hcodim hphase hdiag hfixed hweighted
  let ρ : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ := fun ax cy =>
    ∑ t : Fin 4, (lam t : ℂ) * ppt_qutrit_bell_vector t ax * star (ppt_qutrit_bell_vector t cy)
  have hρ : ρ = ppt_qutrit_bell_state := by
    ext ax cy
    simp [ρ, ppt_qutrit_bell_state, lam, Fin.sum_univ_four, Matrix.sum_apply,
      Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply, Complex.real_smul, mul_assoc]
  let M : Matrix (Fin 3) (Fin 3) ℂ := fun x y => ∑ i : Fin 3, ppt_qutrit_bell_state (i,x) (i,y)
  have hsum' : (∑ s, G s) = Wᴴ*M*W := by
    rw [hsum]
    ext p q
    change (∑ x : Fin 3, ∑ y : Fin 3, star (W x p) *
      (∑ i : Fin 3, ρ (i,x) (i,y)) * W y q) = _
    rw [hρ]
    exact in770_rk2_filter_matrix_entries W M p q
  have hsum1 : (∑ s, G s) = 1 := by
    rw [hsum']
    change (N*U)ᴴ*M*(N*U) = 1
    calc
      (N*U)ᴴ*M*(N*U) = Uᴴ*(Nᴴ*M*N)*U := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = Uᴴ*U := by rw [in770_rk2_normalizer_hermitian, hmarginal]; simp
      _ = 1 := hU
  have hmeas' : ∀ j : Fin 3, (∑ s, if s j then G s else 0) = Uᴴ*ppt_qutrit_steered_effect j*U := by
    intro j
    rw [hmeas j]
    ext p q
    change (∑ x : Fin 3, ∑ y : Fin 3, star (W x p) *
      (∑ i : Fin 3, ∑ k : Fin 3, ρ (i,x) (k,y) * A j k i) * W y q) = _
    rw [hρ]
    let S : Matrix (Fin 3) (Fin 3) ℂ := ppt_qutrit_steered_unnormalized_effect j
    have hs : (fun x y => ∑ i : Fin 3, ∑ k : Fin 3, ppt_qutrit_bell_state (i,x) (k,y) * A j k i) = S := rfl
    rw [show (∑ x : Fin 3, ∑ y : Fin 3, star (W x p) *
      (∑ i : Fin 3, ∑ k : Fin 3, ppt_qutrit_bell_state (i,x) (k,y) * A j k i) * W y q) = (Wᴴ*S*W) p q from by
        change (∑ x : Fin 3, ∑ y : Fin 3, star (W x p) * S x y * W y q) = _
        exact in770_rk2_filter_matrix_entries W S p q]
    have hmat : (N*U)ᴴ*S*(N*U) = Uᴴ*ppt_qutrit_steered_effect j*U := by
      rw [Matrix.conjTranspose_mul, in770_rk2_normalizer_hermitian]
      simp [N, S, ppt_qutrit_steered_effect, Matrix.mul_assoc]
    exact congrArg (fun L : Matrix (Fin 2) (Fin 2) ℂ => L p q) hmat
  obtain ⟨H, hH, hHsum, hHmarg⟩ := in770_rk2_lift_qubit_parent ppt_qutrit_steered_effect U G hG hsum1 hmeas'
  exact ⟨H, hH, by simpa [hUP] using hHsum, by simpa [hUP] using hHmarg⟩

theorem ppt_qutrit_steered_effect_all_proper_subspaces_compatible : ∀ P : Matrix (Fin 3) (Fin 3) ℂ, P.IsHermitian ∧ P * P = P ∧ P.rank < 3 → ∃ G : (Fin 3 → Bool) → Matrix (Fin 3) (Fin 3) ℂ, (∀ s, (G s).PosSemidef) ∧ (∑ s, G s = P) ∧ ∀ j : Fin 3, (∑ s, if s j then G s else 0) = P * ppt_qutrit_steered_effect j * P := by
  have hselect := ppt_qutrit_source_projection_basis_from_isometry_factor
    rank_two_qutrit_projection_isometry
  have hgram := ppt_qutrit_source_normalized_gram_if_three_lemmas hselect
    ppt_qutrit_bell_state_partial_transpose_invariant real_positive_qutrit_gram_normalizer
  have htwo := in770_rk2_rank_two_source_compatibility_if_lemmas hgram
    ppt_qutrit_bell_alice_binary_effects_valid
    ppt_qutrit_steered_normalizer_marginal_identity
    three_orthonormal_rows_codimension_one
    rank_four_ppt_normal_completion_phase
    real_symmetric_commuting_pair_orthogonal_diagonalization
    qutrit_fixed_phase_schur_four_product_decomposition
    (finite_weighted_three_binary_hidden_model_has_parent 2 4)
  intro P ⟨hP, hPP, hrank⟩
  by_cases h2 : P.rank = 2
  · exact htwo P hP hPP h2
  · exact rank_one_qutrit_compression_three_binary_parent
      ppt_qutrit_steered_effect P ppt_qutrit_steered_effect_is_valid hP hPP (by omega)
