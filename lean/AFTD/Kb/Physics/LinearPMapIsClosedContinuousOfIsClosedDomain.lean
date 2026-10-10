import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapIsClosedIsClosedToFunGraph

/-!
# LinearPMap.IsClosed.continuous_of_isClosed_domain

Topic: quantum_mechanics   Node: 60d5c61ff69a

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.IsClosed.continuous_of_isClosed_domain`. Lean proof by Adam Bornemann, Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/Unbounded.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The **closed graph theorem** for partial linear maps: a closed operator with closed domain is continuous. This follows immediately from `LinearMap.continuous_of_isClosed_graph` and the completeness of `H` and `H'`.
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
/-- The **closed graph theorem** for partial linear maps: a closed operator with closed domain is continuous. This follows immediately from `LinearMap.continuous_of_isClosed_graph` and the completeness of `H` and `H'`. -/
lemma LinearPMap.IsClosed.continuous_of_isClosed_domain [CompleteSpace H] [CompleteSpace H']
    (hU : U.IsClosed) (h : _root_.IsClosed (U.domain : Set H)) :
    Continuous U := by
  have : CompleteSpace U.domain := instCompleteSpaceSubtypeMemSubmoduleOfIsClosedCoe U.domain
  exact LinearMap.continuous_of_isClosed_graph U.toFun hU.isClosed_toFun_graph
