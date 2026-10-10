import AFTD.Prelude
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrameVectorDispEquiv

/-!
# Physlib.Wirtinger.conjCLM

Topic: classical_mechanics   Node: fb11379d5593

Provenance: formalization of a published result. Source: Physlib, `Physlib.Wirtinger.conjCLM`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Wirtinger/Coordinate.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Pointwise conjugation bundled as an ℝ-linear CLM (conjugate-ℂ-linear): the I-th component is conjugation of the I-th coordinate `Complex.conjCLE ∘ proj I`. Its underlying function is the `star` of `ι → ℂ` (`conjCLM_apply`). Bundling `star` as a `→L[ℝ]` is what lets the anti-holomorphic lemmas below feed it to the foundation `dWirtingerDir_comp_conjLinear`, which requires its domain map as a continuous linear map.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {ι : Type*} in
variable [Fintype ι] [DecidableEq ι] in
variable {f g : (ι → ℂ) → ℂ} in
/-- Pointwise conjugation bundled as an ℝ-linear CLM (conjugate-ℂ-linear): the I-th component is conjugation of the I-th coordinate `Complex.conjCLE ∘ proj I`. Its underlying function is the `star` of `ι → ℂ` (`conjCLM_apply`). Bundling `star` as a `→L[ℝ]` is what lets the anti-holomorphic lemmas below feed it to the foundation `dWirtingerDir_comp_conjLinear`, which requires its domain map as a continuous linear map. -/
noncomputable def Physlib.Wirtinger.conjCLM : (ι → ℂ) →L[ℝ] (ι → ℂ) :=
  ContinuousLinearMap.pi
    (fun I => Complex.conjCLE.toContinuousLinearMap.comp (ContinuousLinearMap.proj (R := ℝ) I))
