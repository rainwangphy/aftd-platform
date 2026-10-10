import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapClosureDomainLeDomainClosure
import AFTD.Kb.Physics.LinearMapContinuousIffBounded
import AFTD.Kb.Physics.LinearPMapIsClosableOfContinuous
import AFTD.Kb.Physics.StandardModelGaugeGroupIOfU1Subgroup

/-!
# LinearPMap.closure_domain_eq_domain_closure_of_continuous

Topic: quantum_mechanics   Node: 0df769cc1b68

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.closure_domain_eq_domain_closure_of_continuous`. Lean proof by Adam Bornemann, Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/Unbounded.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A strengthening of `closure_domain_le_domain_closure` for continuous operators.
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
/-- A strengthening of `closure_domain_le_domain_closure` for continuous operators. -/
lemma LinearPMap.closure_domain_eq_domain_closure_of_continuous [CompleteSpace H'] (h : Continuous U) :
    U.closure.domain = U.domain.closure := by
  refine eq_of_le_of_ge U.closure_domain_le_domain_closure fun x hx ↦ ?_
  obtain ⟨M, hM, h_bound⟩ := LinearMap.continuous_iff_bounded.mp h
  obtain ⟨b, hb, hb'⟩ := mem_closure_iff_seq_limit.mp hx
  simp only [coe_toAddSubmonoid, SetLike.mem_coe] at hb
  let Ub : ℕ → H' := fun n ↦ U ⟨b n, hb n⟩
  have hCS : CauchySeq Ub := by
    refine Metric.cauchySeq_iff'.mpr fun ε hε ↦ ?_
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.mp hb'.cauchySeq (M⁻¹ * ε) (by positivity)
    refine ⟨N, fun n hn ↦ ?_⟩
    refine lt_of_le_of_lt ?_ ((lt_inv_mul_iff₀ hM).mp (hN n hn))
    calc
      _ = ‖Ub n - Ub N‖ := dist_eq_norm _ _
      _ = ‖U (⟨b n, hb n⟩ - ⟨b N, hb N⟩)‖ := by simp [Ub, map_sub]
      _ ≤ M * ‖b n - b N‖ := h_bound _
      _ = M * dist (b n) (b N) := by rw [dist_eq_norm]
  obtain ⟨y, hy⟩ := CompleteSpace.complete hCS
  apply mem_domain_iff.mpr
  rw [← (isClosable_of_continuous h).graph_closure_eq_closure_graph]
  use y
  refine mem_closure_iff_seq_limit.mpr ⟨fun n ↦ (b n, Ub n), fun n ↦ ?_, ?_⟩
  · simp [hb n, Ub]
  · rw [nhds_prod_eq]
    exact Filter.Tendsto.prodMk hb' hy
