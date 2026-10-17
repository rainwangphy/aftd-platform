import AFTD.Prelude
import AFTD.Kb.Tcs.ComplexLaplaceIntegrand

/-!
# ComplexLaplaceEndpointEnvelope

Topic: quantum   Node: 8e41841d9984

Provenance: formalization of a published result. Source: QuantumInfo, `ComplexLaplaceEndpointEnvelope`. Lean proof by Dennj Osele, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/ComplexLaplaceTransform.lean (Copyright (c) 2025 Dennj Osele. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

ComplexLaplaceEndpointEnvelope
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
noncomputable def ComplexLaplaceEndpointEnvelope {α : Type*} (E : α → WithTop ℝ) (z w : ℂ)
    (x : α) : ℝ :=
  ‖ComplexLaplaceIntegrand E z x‖ + ‖ComplexLaplaceIntegrand E w x‖
