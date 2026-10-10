import AFTD.Prelude
import AFTD.Kb.Tcs.DimMapRE
import AFTD.Kb.Physics.StandardModelGaugeGroupIOfU1Subgroup
import AFTD.Kb.GameTheoryEconomics.CatchUpValueEqDrawIffNotLoss

/-!
# LinearPMap.IsClosable.add_continuous

Topic: quantum_mechanics   Node: 40d05b8fa07a

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.IsClosable.add_continuous`. Lean proof by Adam Bornemann, Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/Unbounded.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Closability is preserved upon adding a continuous operator.
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
/-- Closability is preserved upon adding a continuous operator. -/
lemma LinearPMap.IsClosable.add_continuous
    (h₁ : U₁.IsClosable) (h₂ : Continuous U₂) (h : U₁.domain ≤ U₂.domain) :
    (U₁ + U₂).IsClosable := by
  use (U₁ + U₂).graph.topologicalClosure.toLinearPMap
  refine (toLinearPMap_graph_eq _ fun ⟨x₁, x₂⟩ hx hx₁ ↦ ?_).symm
  subst hx₁
  refine graph_fst_eq_zero_snd U₁.closure ?_ rfl
  rw [← h₁.graph_closure_eq_closure_graph]
  apply mem_closure_iff_seq_limit.mpr
  obtain ⟨b, hb, hbx⟩ := mem_closure_iff_seq_limit.mp hx
  simp only [coe_toAddSubmonoid, SetLike.mem_coe, mem_graph_iff, add_domain, add_apply,
    Subtype.exists, exists_and_left, exists_eq_left, nhds_prod_eq] at *
  refine ⟨fun n ↦ ((b n).1, (b n).2 - U₂ ⟨(b n).1, h (hb n).choose.1⟩), fun n ↦ ?_, ?_⟩
  · exact ⟨(hb n).choose.1, eq_sub_of_add_eq (hb n).choose_spec⟩
  · refine Filter.Tendsto.prodMk hbx.fst ?_
    refine sub_zero x₂ ▸ hbx.snd.sub ?_
    exact map_zero U₂ ▸ (h₂.tendsto 0).comp (tendsto_subtype_rng.mpr hbx.fst)
