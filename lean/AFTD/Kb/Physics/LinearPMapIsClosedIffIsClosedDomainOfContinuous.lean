import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapIsClosableIsClosedIff
import AFTD.Kb.Physics.LinearPMapIsClosableOfContinuous
import AFTD.Kb.Physics.LinearPMapClosureDomainEqDomainClosureOfContinuous

/-!
# LinearPMap.isClosed_iff_isClosed_domain_of_continuous

Topic: quantum_mechanics   Node: 8f33418b3680

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.isClosed_iff_isClosed_domain_of_continuous`. Lean proof by Adam Bornemann, Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/Unbounded.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A continuous operator is closed iff its domain is closed.
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
/-- A continuous operator is closed iff its domain is closed. -/
lemma LinearPMap.isClosed_iff_isClosed_domain_of_continuous [CompleteSpace H'] (h : Continuous U) :
    U.IsClosed ↔ _root_.IsClosed (U.domain : Set H) := by
  rw [(isClosable_of_continuous h).isClosed_iff]
  have h_domain := closure_domain_eq_domain_closure_of_continuous h
  constructor <;> intro hcl
  · exact hcl ▸ h_domain ▸ isClosed_closure
  · refine (eq_of_le_of_domain_eq U.le_closure ?_).symm
    exact h_domain ▸ hcl.submodule_topologicalClosure_eq.symm
