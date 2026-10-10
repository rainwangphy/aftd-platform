import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapHasDenseDomain

/-!
# LinearPMap.adjoint_of_zero

Topic: quantum_mechanics   Node: 261c8ddef01a

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.adjoint_of_zero`. Lean proof by Adam Bornemann, Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/Unbounded.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The adjoint of a zero LinearPMap (any domain) is zero (domain `⊤`).
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
/-- The adjoint of a zero LinearPMap (any domain) is zero (domain `⊤`). -/
lemma LinearPMap.adjoint_of_zero [CompleteSpace H] (h_zero : ⇑U = 0) : U† = 0 := by
  refine dExt ?_ fun x y hxy ↦ ?_
  · ext
    simp only [zero_domain, mem_top, iff_true]
    exact (mem_adjoint_domain_iff _ _).mpr (continuous_of_const (by simp [h_zero]))
  · by_cases h : U.HasDenseDomain
    · exact adjoint_apply_eq h x (by simp [h_zero])
    · exact adjoint_apply_of_not_dense h x
