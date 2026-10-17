import AFTD.Prelude
import AFTD.Kb.Tcs.ComplexLaplaceIntegrand

/-!
# ComplexLaplaceTransform

Topic: quantum   Node: fce67217c25e

Provenance: formalization of a published result. Source: QuantumInfo, `ComplexLaplaceTransform`. Lean proof by Dennj Osele, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/ComplexLaplaceTransform.lean (Copyright (c) 2025 Dennj Osele. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The complex Laplace transform of a possibly infinite-valued energy function.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The complex Laplace transform of a possibly infinite-valued energy function. -/
noncomputable def ComplexLaplaceTransform {α : Type*} [MeasureTheory.MeasureSpace α]
    (E : α → WithTop ℝ) (z : ℂ) : ℂ :=
  ∫ x, ComplexLaplaceIntegrand E z x
