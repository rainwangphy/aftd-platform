import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibWirtingerWeightedDirDeriv
import AFTD.Kb.Physics.PhyslibWirtingerHasFDerivAtFderivApply
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumSeparatrixEnergy

/-!
# Physlib.Wirtinger.hasFDerivAt_weightedDirDeriv

Topic: classical_mechanics   Node: 04510cfdb703

Provenance: formalization of a published result. Source: Physlib, `Physlib.Wirtinger.hasFDerivAt_weightedDirDeriv`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Wirtinger/Basic.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The `weightedDirDeriv` is differentiable wherever `fderiv ℝ f` is.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib Physlib.Wirtinger in
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
  {f : V → ℂ} {u : V} in
omit [NormedSpace ℂ V] in
/-- The `weightedDirDeriv` is differentiable wherever `fderiv ℝ f` is. -/
lemma Physlib.Wirtinger.hasFDerivAt_weightedDirDeriv (hf' : DifferentiableAt ℝ (fderiv ℝ f) u)
    (c : ℂ) (b₁ b₂ : V) :
    HasFDerivAt (weightedDirDeriv f c b₁ b₂)
      ((1 / 2 : ℂ) • ((ContinuousLinearMap.apply ℝ ℂ b₁).comp (fderiv ℝ (fderiv ℝ f) u)
        + c • (ContinuousLinearMap.apply ℝ ℂ b₂).comp (fderiv ℝ (fderiv ℝ f) u))) u :=
  ((hasFDerivAt_fderiv_apply hf' b₁).add
    ((hasFDerivAt_fderiv_apply hf' b₂).const_mul c)).const_mul (1 / 2)
