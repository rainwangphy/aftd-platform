import AFTD.Prelude

/-!
# LinearPMap.HasDenseDomain

Topic: quantum_mechanics   Node: 7a2b50cfd67c

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.HasDenseDomain`. Lean proof by Adam Bornemann, Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/Unbounded.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A LinearPMap `U` has dense domain iff `U.domain` is dense in `H`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
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
/-- A LinearPMap `U` has dense domain iff `U.domain` is dense in `H`. -/
def LinearPMap.HasDenseDomain (U : H →ₗ.[ℂ] H') : Prop := Dense (U.domain : Set H)
