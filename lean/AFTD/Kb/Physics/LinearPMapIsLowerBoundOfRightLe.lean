import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapIsLowerBound

/-!
# LinearPMap.isLowerBound_of_right_le

Topic: quantum_mechanics   Node: f3d9718b0d1e

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.isLowerBound_of_right_le`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/SpectralTheory/Basic.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearPMap.isLowerBound_of_right_le
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
open Submodule in
open Metric in
open InnerProductSpace in
open Complex in
open ComplexConjugate in
open Set in
open Pointwise in
lemma LinearPMap.isLowerBound_of_right_le
    {T : H →ₗ.[ℂ] H} {z : ℂ} {c₁ c₂ : ℝ} (hle : c₁ ≤ c₂) (h : IsLowerBound T z c₂) :
    IsLowerBound T z c₁ :=
  fun x ↦ (mul_le_mul_of_nonneg_right hle (norm_nonneg x)).trans (h x)
