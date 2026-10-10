import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapCentered

/-!
# LinearPMap.variance

Topic: quantum_mechanics   Node: 01a68f13b14a

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.variance`. Lean proof by Matteo Cipollina, Krystian Nowakowski, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/StateObservables/Variance.lean (Copyright (c) 2026 Axiomatic-AI. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Variance `‖Tψ - ⟨T⟩_ψ ψ‖ ^ 2`; only `ψ ∈ T.domain` is required.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
open InnerProductSpace in
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
/-- Variance `‖Tψ - ⟨T⟩_ψ ψ‖ ^ 2`; only `ψ ∈ T.domain` is required. -/
noncomputable def LinearPMap.variance (T : H →ₗ.[ℂ] H) (ψ : T.domain) : ℝ :=
  ‖centered T ψ‖ ^ 2
