import AFTD.Prelude
import AFTD.Kb.Tcs.DimMapRE
import AFTD.Kb.Physics.StandardModelGaugeGroupIOfU1Subgroup
import AFTD.Kb.GameTheoryEconomics.CatchUpValueEqDrawIffNotLoss

/-!
# LinearPMap.closure_domain_le_domain_closure

Topic: quantum_mechanics   Node: 487edcb081f0

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.closure_domain_le_domain_closure`. Lean proof by Adam Bornemann, Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/Unbounded.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearPMap.closure_domain_le_domain_closure
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
lemma LinearPMap.closure_domain_le_domain_closure (U : H →ₗ.[ℂ] H') : U.closure.domain ≤ U.domain.closure := by
  by_cases h_cl : U.IsClosable
  · intro ψ hψ
    obtain ⟨φ, hψφ⟩ := h_cl.graph_closure_eq_closure_graph ▸ mem_domain_iff.mp hψ
    obtain ⟨b, hb, hb'⟩ := mem_closure_iff_seq_limit.mp hψφ
    refine mem_closure_iff_seq_limit.mpr
      ⟨fun n ↦ (b n).1, fun n ↦ ?_, (nhds_prod_eq (x := ψ) (y := φ) ▸ hb').fst⟩
    simp only [coe_toAddSubmonoid, SetLike.mem_coe, mem_graph_iff, Subtype.exists,
      exists_and_left, exists_eq_left] at hb
    exact (hb n).choose
  · simp [closure_def' h_cl, closure_le.mp]
