import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapHasDenseDomain
import AFTD.Kb.Tcs.DimMapRE
import AFTD.Kb.Physics.LinearPMapCompRestrictedDomain
import AFTD.Kb.Tcs.KerRE
import AFTD.Kb.GameTheoryEconomics.CatchUpValueEqDrawIffNotLoss

/-!
# LinearPMap.HasDenseDomain.orthogonal_range

Topic: quantum_mechanics   Node: f2402e50e691

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.HasDenseDomain.orthogonal_range`. Lean proof by Adam Bornemann, Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/Unbounded.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`U.rangeᗮ = U†.ker` c.f. `LinearMap.orthogonal_range` and `ContinuousLinearMap.orthogonal_range`
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
/-- `U.rangeᗮ = U†.ker` c.f. `LinearMap.orthogonal_range` and `ContinuousLinearMap.orthogonal_range` -/
lemma LinearPMap.HasDenseDomain.orthogonal_range [CompleteSpace H] (h : U.HasDenseDomain) :
    U.toFun.rangeᗮ = U†.toFun.ker.map U†.domain.subtype := by
  ext u
  simp only [mem_orthogonal', Subtype.exists, mem_map, LinearMap.mem_ker, subtype_apply,
    exists_and_right, exists_eq_right, toFun_eq_coe]
  constructor
  · intro h'
    exact ⟨mem_adjoint_domain_of_exists u ⟨0, by simp [h']⟩, adjoint_apply_eq h _ (by simp [h'])⟩
  · intro ⟨hu, hu'⟩ v ⟨x, hxv⟩
    simp [← hxv, ← adjoint_isFormalAdjoint h ⟨u, hu⟩, hu']
