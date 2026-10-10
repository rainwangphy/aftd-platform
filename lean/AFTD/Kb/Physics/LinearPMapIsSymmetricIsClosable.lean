import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapIsSymmetric
import AFTD.Kb.Physics.LinearPMapHasDenseDomain

/-!
# LinearPMap.IsSymmetric.isClosable

Topic: quantum_mechanics   Node: 733f022307a3

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.IsSymmetric.isClosable`. Lean proof by Adam Bornemann, Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/Unbounded.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearPMap.IsSymmetric.isClosable
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
lemma LinearPMap.IsSymmetric.isClosable [CompleteSpace H] (h : T.IsSymmetric) (h' : T.HasDenseDomain) :
    T.IsClosable :=
  isClosable_iff_exists_closed_extension.mpr ⟨T†, adjoint_isClosed h', h.le_adjoint h'⟩
