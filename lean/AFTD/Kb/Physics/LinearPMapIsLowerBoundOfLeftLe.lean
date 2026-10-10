import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapIsLowerBound

/-!
# LinearPMap.isLowerBound_of_left_le

Topic: quantum_mechanics   Node: 93ae3d906f42

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.isLowerBound_of_left_le`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/SpectralTheory/Basic.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearPMap.isLowerBound_of_left_le
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
lemma LinearPMap.isLowerBound_of_left_le
    {T₁ T₂ : H →ₗ.[ℂ] H} (hle : T₁ ≤ T₂) {z : ℂ} {c : ℝ} (h : IsLowerBound T₂ z c) :
    IsLowerBound T₁ z c :=
  fun x ↦ @hle.2 x ⟨x, hle.1 x.2⟩ rfl ▸ h ⟨x, hle.1 x.2⟩
