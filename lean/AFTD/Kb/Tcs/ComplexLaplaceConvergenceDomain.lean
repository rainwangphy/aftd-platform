import AFTD.Prelude
import AFTD.Kb.Tcs.ComplexLaplaceIntegrand

/-!
# ComplexLaplaceConvergenceDomain

Topic: quantum   Node: 51ee718d7dea

Provenance: formalization of a published result. Source: QuantumInfo, `ComplexLaplaceConvergenceDomain`. Lean proof by Dennj Osele, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/ComplexLaplaceTransform.lean (Copyright (c) 2025 Dennj Osele. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The complex convergence domain of a Laplace transform.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The complex convergence domain of a Laplace transform. -/
noncomputable def ComplexLaplaceConvergenceDomain {α : Type*} [MeasureTheory.MeasureSpace α]
    (E : α → WithTop ℝ) : Set ℂ :=
  {z | MeasureTheory.Integrable (μ := MeasureTheory.volume) (ComplexLaplaceIntegrand E z)}
