import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapHasDenseDomain
import AFTD.Kb.Physics.LinearPMapAdjointAddLeAddAdjoint
import AFTD.Kb.Physics.LinearPMapAdjointNeg

/-!
# LinearPMap.adjoint_sub_le_sub_adjoint

Topic: quantum_mechanics   Node: 0d78daefccdb

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.adjoint_sub_le_sub_adjoint`. Lean proof by Adam Bornemann, Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/Unbounded.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearPMap.adjoint_sub_le_sub_adjoint
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
lemma LinearPMap.adjoint_sub_le_sub_adjoint [CompleteSpace H]
    (U₁ U₂ : H →ₗ.[ℂ] H') (h₁₂ : (U₁ - U₂).HasDenseDomain) : U₁† - U₂† ≤ (U₁ - U₂)† := by
  simp only [sub_eq_add_neg, ← adjoint_neg]
  exact adjoint_add_le_add_adjoint U₁ (-U₂) h₁₂
