import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapVariance
import AFTD.Kb.Physics.LinearPMapExpectedValue

/-!
# LinearPMap.variance_eq_norm_sub_sq

Topic: quantum_mechanics   Node: 1c407df63dea

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.variance_eq_norm_sub_sq`. Lean proof by Matteo Cipollina, Krystian Nowakowski, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/StateObservables/Variance.lean (Copyright (c) 2026 Axiomatic-AI. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`variance` with `centered` unfolded to `Tψ - ⟨T⟩_ψ • ψ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
open InnerProductSpace in
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
/-- `variance` with `centered` unfolded to `Tψ - ⟨T⟩_ψ • ψ`. -/
lemma LinearPMap.variance_eq_norm_sub_sq (T : H →ₗ.[ℂ] H) (ψ : T.domain) :
    variance T ψ =
      ‖T ψ - (expectedValue T ψ : ℂ) • (ψ : H)‖ ^ 2 :=
  rfl
