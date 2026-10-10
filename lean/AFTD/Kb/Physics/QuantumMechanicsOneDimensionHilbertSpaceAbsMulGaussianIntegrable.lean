import AFTD.Prelude
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceMemHS
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceMulGaussianMemLpOne
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceToBraApply
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceZeroMemHS
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceZeroFunMemHS
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceELpNormMk
import AFTD.Kb.Physics.CondensedMatterTightBindingChainQuantaWaveNumberExpSubOne

/-!
# QuantumMechanics.OneDimension.HilbertSpace.abs_mul_gaussian_integrable

Topic: quantum_mechanics   Node: b81981f09ba9

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.OneDimension.HilbertSpace.abs_mul_gaussian_integrable`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/HilbertSpaces/OneDimension/Gaussians.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

QuantumMechanics.OneDimension.HilbertSpace.abs_mul_gaussian_integrable
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory in
open MeasureTheory in
lemma QuantumMechanics.OneDimension.HilbertSpace.abs_mul_gaussian_integrable (f : ℝ → ℂ) (hf : MemHS f) (b c : ℝ) (hb : 0 < b) :
    MeasureTheory.Integrable (fun x => norm (f x) * Real.exp (- b * (x - c)^2)) := by
  have h1 : (fun x => norm (f x) * Real.exp (- b * (x - c)^2)) =
      (fun x => norm (f x * Real.exp (- b *(x - c)^2))) := by
    funext x
    simp only [neg_mul, Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_mul,
      Complex.ofReal_pow, Complex.ofReal_sub, Complex.norm_mul, Complex.norm_exp, Complex.neg_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, mul_eq_mul_left_iff,
      Real.exp_eq_exp, neg_inj, norm_eq_zero]
    left
    left
    simp [← Complex.ofReal_sub, ← Complex.ofReal_pow]
  rw [h1]
  simpa using MeasureTheory.MemLp.integrable_norm_rpow (mul_gaussian_mem_Lp_one f hf b c hb)
    one_ne_zero ENNReal.one_ne_top
