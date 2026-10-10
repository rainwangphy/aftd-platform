import AFTD.Prelude
import AFTD.Kb.Physics.ContinuousLinearMapComplexOfCommutesI

/-!
# ContinuousLinearMap.complexOfCommutesI_apply

Topic: classical_mechanics   Node: 696df683f1ad

Provenance: formalization of a published result. Source: Physlib, `ContinuousLinearMap.complexOfCommutesI_apply`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/ComplexLinear.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

ContinuousLinearMap.complexOfCommutesI_apply
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ContinuousLinearMap in
variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
@[simp]
lemma ContinuousLinearMap.complexOfCommutesI_apply (L : V →L[ℝ] E)
    (h : ∀ v, L (Complex.I • v) = Complex.I • L v) (v : V) :
    complexOfCommutesI L h v = L v := rfl
