import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapIsClosedAddContinuous

/-!
# LinearPMap.IsClosed.sub_continuous

Topic: quantum_mechanics   Node: 9eef6123ff5d

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.IsClosed.sub_continuous`. Lean proof by Adam Bornemann, Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/Unbounded.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Closedness is preserved upon subtracting a continuous operator.
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
/-- Closedness is preserved upon subtracting a continuous operator. -/
lemma LinearPMap.IsClosed.sub_continuous [CompleteSpace H']
    (h₁ : U₁.IsClosed) (h₂ : Continuous U₂) (h : U₁.domain ≤ U₂.domain) : (U₁ - U₂).IsClosed :=
  sub_eq_add_neg U₁ U₂ ▸ h₁.add_continuous h₂.neg h
