import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapHasDenseDomain
import AFTD.Kb.Physics.LinearPMapHasDenseDomainOrthogonalRange
import AFTD.Kb.Physics.LinearPMapHasDenseDomainClosure

/-!
# LinearPMap.HasDenseDomain.orthogonal_adjoint_ker

Topic: quantum_mechanics   Node: 6989f7e66bf1

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.HasDenseDomain.orthogonal_adjoint_ker`. Lean proof by Adam Bornemann, Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/Unbounded.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`U†.kerᗮ = U.range.closure`
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
/-- `U†.kerᗮ = U.range.closure` -/
lemma LinearPMap.HasDenseDomain.orthogonal_adjoint_ker [CompleteSpace H] [CompleteSpace H']
    (h : U.HasDenseDomain) :
    (U†.toFun.ker.map U†.domain.subtype)ᗮ = U.toFun.range.closure :=
  h.orthogonal_range ▸ orthogonal_orthogonal_eq_closure _
