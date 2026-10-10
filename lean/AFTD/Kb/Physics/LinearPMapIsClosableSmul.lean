import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapIsClosableOfZero
import AFTD.Kb.Physics.LinearPMapClosureDomainLeDomainClosure
import AFTD.Kb.Physics.StandardModelGaugeGroupIOfU1Subgroup
import AFTD.Kb.GameTheoryEconomics.CatchUpValueEqDrawIffNotLoss

/-!
# LinearPMap.IsClosable.smul

Topic: quantum_mechanics   Node: b9dfac1c66c5

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.IsClosable.smul`. Lean proof by Adam Bornemann, Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/Unbounded.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearPMap.IsClosable.smul
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
@[aesop safe apply]
lemma LinearPMap.IsClosable.smul (h : U.IsClosable) (c : ℂ) : (c • U).IsClosable := by
  rcases eq_zero_or_neZero c with (rfl | hc)
  · exact isClosable_of_zero (by simp)
  · use (c • U).graph.topologicalClosure.toLinearPMap
    refine (toLinearPMap_graph_eq _ fun x hx hx₁ ↦ ?_).symm
    rw [← smul_zero c, ← inv_smul_eq_iff₀ hc.ne]
    refine graph_fst_eq_zero_snd U.closure ?_ rfl
    rw [← h.graph_closure_eq_closure_graph]
    apply mem_closure_iff_seq_limit.mpr
    obtain ⟨b, hb, hb'⟩ := mem_closure_iff_seq_limit.mp hx
    use fun n ↦ ((b n).fst, c⁻¹ • (b n).snd)
    rw [nhds_prod_eq, Filter.tendsto_prod_iff'] at *
    refine ⟨fun n ↦ ?_, hx₁ ▸ hb'.1, hb'.2.const_smul c⁻¹⟩
    obtain ⟨u, hu, hu'⟩ := hb n
    simp only [coe_toAddSubmonoid, SetLike.mem_coe, mem_graph_iff, Subtype.exists, ← hu']
    exact ⟨u.1, u.1.2, rfl, ((inv_smul_eq_iff₀ hc.ne).mpr hu).symm⟩
