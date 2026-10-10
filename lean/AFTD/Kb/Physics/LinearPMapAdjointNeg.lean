import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapNegEqNegOneSmul
import AFTD.Kb.Physics.LinearPMapAdjointSmul

/-!
# LinearPMap.adjoint_neg

Topic: quantum_mechanics   Node: b577f2424450

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.adjoint_neg`. Lean proof by Adam Bornemann, Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/Unbounded.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearPMap.adjoint_neg
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
@[simp]
lemma LinearPMap.adjoint_neg [CompleteSpace H] (U : H →ₗ.[ℂ] H') : (-U)† = -U† := by
  simp [neg_eq_neg_one_smul, adjoint_smul]
