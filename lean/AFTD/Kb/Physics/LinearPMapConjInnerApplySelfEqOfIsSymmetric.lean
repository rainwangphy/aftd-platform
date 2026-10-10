import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapIsSymmetric

/-!
# LinearPMap.conj_inner_apply_self_eq_of_isSymmetric

Topic: quantum_mechanics   Node: 085ef703b446

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.conj_inner_apply_self_eq_of_isSymmetric`. Lean proof by Matteo Cipollina, Krystian Nowakowski, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/StateObservables/ExpectedValue.lean (Copyright (c) 2026 Axiomatic-AI. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearPMap.conj_inner_apply_self_eq_of_isSymmetric
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
open InnerProductSpace in
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
lemma LinearPMap.conj_inner_apply_self_eq_of_isSymmetric (T : H →ₗ.[ℂ] H) (hT : T.IsSymmetric)
    (ψ : T.domain) :
    (starRingEnd ℂ) ⟪(ψ : H), T ψ⟫_ℂ = ⟪(ψ : H), T ψ⟫_ℂ := by
  simpa [inner_conj_symm] using hT ψ ψ
