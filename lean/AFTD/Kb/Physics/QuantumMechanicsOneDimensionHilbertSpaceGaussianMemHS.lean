import AFTD.Prelude
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceMemHS
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceMemHSIff
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceGaussianAestronglyMeasurable
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceToBraApply
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceZeroMemHS
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceZeroFunMemHS
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceELpNormMk

/-!
# QuantumMechanics.OneDimension.HilbertSpace.gaussian_memHS

Topic: quantum_mechanics   Node: 4f6c4d92a691

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.OneDimension.HilbertSpace.gaussian_memHS`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/HilbertSpaces/OneDimension/Gaussians.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

QuantumMechanics.OneDimension.HilbertSpace.gaussian_memHS
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory in
open MeasureTheory in
lemma QuantumMechanics.OneDimension.HilbertSpace.gaussian_memHS {b : ℝ} (c : ℝ) (hb : 0 < b) :
    MemHS (fun x => (Real.exp (- b * (x - c) ^2) : ℂ)) := by
  rw [memHS_iff]
  refine ⟨gaussian_aestronglyMeasurable c hb, ?_⟩
  simp only [neg_mul, Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_mul,
    Complex.ofReal_pow, Complex.ofReal_sub, Complex.norm_exp, Complex.neg_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have h1 : (fun (x : ℝ) => Real.exp (-(b * ((x - c : ℂ) ^ 2).re)) ^ 2) =
    fun y => (fun x => Real.exp (- (2 * b) * x ^ 2)) (y - c) := by
    ext x
    simp only [neg_mul]
    trans Real.exp (-(b * ((x - c: ℂ) ^ 2).re)) ^ (2 : ℝ)
    · simp
    rw [← Real.exp_mul]
    simp only [neg_mul, Real.exp_eq_exp, neg_inj]
    rw [← Complex.ofReal_sub, ← Complex.ofReal_pow, Complex.ofReal_re]
    ring
  rw [h1]
  apply Integrable.comp_sub_right (f := fun x => Real.exp (- (2 * b) * x ^ 2))
  apply integrable_exp_neg_mul_sq
  simp_all
