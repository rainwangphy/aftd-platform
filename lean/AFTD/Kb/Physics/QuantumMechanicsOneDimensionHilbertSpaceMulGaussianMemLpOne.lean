import AFTD.Prelude
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceMemHS
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpace
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceMk
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceGaussianMemHS
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceCoeMkAe
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceToBraApply
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceZeroMemHS
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceZeroFunMemHS
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceELpNormMk

/-!
# QuantumMechanics.OneDimension.HilbertSpace.mul_gaussian_mem_Lp_one

Topic: quantum_mechanics   Node: 508e4109aa27

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.OneDimension.HilbertSpace.mul_gaussian_mem_Lp_one`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/HilbertSpaces/OneDimension/Gaussians.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

QuantumMechanics.OneDimension.HilbertSpace.mul_gaussian_mem_Lp_one
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory in
open MeasureTheory in
lemma QuantumMechanics.OneDimension.HilbertSpace.mul_gaussian_mem_Lp_one (f : ℝ → ℂ) (hf : MemHS f) (b c : ℝ) (hb : 0 < b) :
    MeasureTheory.MemLp (fun x => f x * Real.exp (- b * (x - c) ^ 2)) 1 volume := by
  refine memLp_one_iff_integrable.mpr ?_
  let g : HilbertSpace := mk (gaussian_memHS c hb)
  refine (integrable_congr ?_).mp (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) g (mk hf))
  simp only [RCLike.inner_apply, neg_mul, Complex.ofReal_exp, Complex.ofReal_neg,
    Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_sub]
  refine Filter.EventuallyEq.mul (coe_mk_ae hf) ?_
  trans (fun x => (starRingEnd ℂ) (Real.exp (- b * (x - c) ^2)))
  · apply Filter.EventuallyEq.fun_comp
    simp only [neg_mul, Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_mul,
      Complex.ofReal_pow, Complex.ofReal_sub, g]
    exact AEEqFun.coeFn_mk ..
  · apply Filter.EventuallyEq.of_eq
    funext x
    rw [Complex.conj_ofReal]
    simp
