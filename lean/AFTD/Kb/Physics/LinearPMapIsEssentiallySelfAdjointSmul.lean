import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapIsEssentiallySelfAdjoint
import AFTD.Kb.Physics.LinearPMapClosureSmul
import AFTD.Kb.Physics.LinearPMapAdjointSmul
import AFTD.Kb.Physics.LinearPMapIsEssentiallySelfAdjointDef
import AFTD.Kb.Physics.LinearPMapIsUnboundedAdjointClosureEqAdjoint
import AFTD.Kb.Physics.LinearPMapIsUnboundedAdjointAdjointEqClosure

/-!
# LinearPMap.IsEssentiallySelfAdjoint.smul

Topic: quantum_mechanics   Node: 45390a204e3a

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.IsEssentiallySelfAdjoint.smul`. Lean proof by Adam Bornemann, Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/Unbounded.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearPMap.IsEssentiallySelfAdjoint.smul
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
open Submodule in
open InnerProductSpace in
open Complex ComplexConjugate in
variable
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  {H'' : Type*} [NormedAddCommGroup H''] [InnerProductSpace ℂ H'']
  {α : Type*} [Fintype α]
  {T T₁ T₂ : H →ₗ.[ℂ] H} {S : α → H →ₗ.[ℂ] H}
  {U U₁ U₂ : H →ₗ.[ℂ] H'} {W : α → H →ₗ.[ℂ] H'}
  {V V₁ V₂ : H' →ₗ.[ℂ] H''} in
variable (u : H ≃ₗᵢ[ℂ] H') (A : H →ₗ.[ℂ] H) in
variable {u A} in
@[aesop safe apply]
lemma LinearPMap.IsEssentiallySelfAdjoint.smul [CompleteSpace H]
    (h : T.IsEssentiallySelfAdjoint) {c : ℂ} (hc : c ≠ 0) (hc' : conj c = c) :
    (c • T).IsEssentiallySelfAdjoint := by
  simp_all [isEssentiallySelfAdjoint_def, isSelfAdjoint_def, closure_smul _ hc, adjoint_smul _ hc]
