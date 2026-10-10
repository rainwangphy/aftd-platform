import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibWirtingerWeightedDirDeriv
import AFTD.Kb.Physics.PhyslibWirtingerHasFDerivAtWeightedDirDeriv

/-!
# Physlib.Wirtinger.fderiv_weightedDirDeriv

Topic: classical_mechanics   Node: a17c8920ebde

Provenance: formalization of a published result. Source: Physlib, `Physlib.Wirtinger.fderiv_weightedDirDeriv`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Wirtinger/Basic.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The bridge: differentiating a `weightedDirDeriv` along a third direction `a` lands on the second real Fréchet derivative `fderiv ℝ (fderiv ℝ f) u a b` in the two slots.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib Physlib.Wirtinger in
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
  {f : V → ℂ} {u : V} in
omit [NormedSpace ℂ V] in
/-- The bridge: differentiating a `weightedDirDeriv` along a third direction `a` lands on the second real Fréchet derivative `fderiv ℝ (fderiv ℝ f) u a b` in the two slots. -/
lemma Physlib.Wirtinger.fderiv_weightedDirDeriv (hf' : DifferentiableAt ℝ (fderiv ℝ f) u)
    (c : ℂ) (b₁ b₂ a : V) :
    fderiv ℝ (weightedDirDeriv f c b₁ b₂) u a
      = (1 / 2 : ℂ) * (fderiv ℝ (fderiv ℝ f) u a b₁
          + c * fderiv ℝ (fderiv ℝ f) u a b₂) := by
  simp only [(hasFDerivAt_weightedDirDeriv hf' c b₁ b₂).fderiv, add_apply, _root_.smul_apply,
    ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.apply_apply,
    smul_eq_mul, mul_add]
