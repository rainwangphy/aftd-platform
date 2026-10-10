import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapIsClosableAddContinuous
import AFTD.Kb.Physics.LinearPMapIsClosableIsClosedIff
import AFTD.Kb.Physics.LinearMapContinuousIffBounded
import AFTD.Kb.Physics.LinearPMapIsClosedClosureEq
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolAuxSubset
import AFTD.Kb.Tcs.DimMapRE
import AFTD.Kb.Physics.StandardModelGaugeGroupIOfU1Subgroup
import AFTD.Kb.GameTheoryEconomics.CatchUpValueEqDrawIffNotLoss

/-!
# LinearPMap.IsClosed.add_continuous

Topic: quantum_mechanics   Node: 5ec426328bcd

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.IsClosed.add_continuous`. Lean proof by Adam Bornemann, Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/Unbounded.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Closedness is preserved upon adding a continuous operator.
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
/-- Closedness is preserved upon adding a continuous operator. -/
lemma LinearPMap.IsClosed.add_continuous [CompleteSpace H']
    (h₁ : U₁.IsClosed) (h₂ : Continuous U₂) (h : U₁.domain ≤ U₂.domain) : (U₁ + U₂).IsClosed := by
  have hcl : (U₁ + U₂).IsClosable := h₁.isClosable.add_continuous h₂ h
  refine hcl.isClosed_iff.mpr (eq_of_le_of_ge (le_of_le_graph ?_) (U₁ + U₂).le_closure)
  rw [← hcl.graph_closure_eq_closure_graph]
  intro ⟨x₁, x₂⟩ hx
  obtain ⟨b, hb, hbx⟩ := mem_closure_iff_seq_limit.mp hx
  simp only [coe_toAddSubmonoid, SetLike.mem_coe, mem_graph_iff, Subtype.exists, exists_and_left,
    exists_eq_left, add_domain, inf_of_le_left h] at hb
  rw [nhds_prod_eq] at hbx
  have hb₁U₂ : ∀ n, (b n).1 ∈ U₂.domain := fun n ↦ h (hb n).choose
  have hCS : CauchySeq fun n ↦ U₂ ⟨(b n).1, hb₁U₂ n⟩ := by
    obtain ⟨M, hM, h_bound⟩ := LinearMap.continuous_iff_bounded.mp h₂
    refine Metric.cauchySeq_iff'.mpr fun ε hε ↦ ?_
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.mp hbx.fst.cauchySeq (M⁻¹ * ε) (by positivity)
    refine ⟨N, fun n hn ↦ ?_⟩
    calc
      _ = ‖U₂ (⟨(b n).1, hb₁U₂ n⟩ - ⟨(b N).1, hb₁U₂ N⟩)‖ := by rw [map_sub, dist_eq_norm]
      _ ≤ M * ‖(b n).1 - (b N).1‖ := h_bound _
      _ < ε := dist_eq_norm (b n).1 (b N).1 ▸ (lt_inv_mul_iff₀ hM).mp (hN n hn)
  obtain ⟨y, hy⟩ := CompleteSpace.complete hCS
  have hU₁ : (x₁, x₂ - y) ∈ U₁.graph := by
    rw [← h₁.closure_eq, ← h₁.isClosable.graph_closure_eq_closure_graph]
    apply mem_closure_iff_seq_limit.mpr
    refine ⟨fun n ↦ ((b n).1, (b n).2 - U₂ ⟨(b n).1, hb₁U₂ n⟩), fun n ↦ ?_, ?_⟩
    · simp_all [add_apply, eq_sub_iff_add_eq]
    · rw [nhds_prod_eq]
      exact hbx.fst.prodMk (hbx.snd.sub hy)
  have hx₁ : x₁ ∈ U₁.domain := mem_domain_of_mem_graph hU₁
  have hU₂y : U₂ ⟨x₁, h hx₁⟩ = y := by
    refine tendsto_nhds_unique ((h₂.tendsto ⟨x₁, h hx₁⟩).comp ?_) (Filter.tendsto_map'_iff.mp hy)
    exact tendsto_subtype_rng.mpr hbx.fst
  simp_all [add_domain, add_apply]
