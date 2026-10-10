import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapIsClosableSmul
import AFTD.Kb.Physics.LinearPMapIsClosableSmulIff
import AFTD.Kb.Physics.LinearPMapCompRestrictedDomain
import AFTD.Kb.GameTheoryEconomics.PersuasionLymSumLe
import AFTD.Kb.Tcs.CommunicationComplexityRectangleIsRectangleIff
import AFTD.Kb.Tcs.DimMapRE

/-!
# LinearPMap.closure_smul

Topic: quantum_mechanics   Node: 273bc660cc6c

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.closure_smul`. Lean proof by Adam Bornemann, Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/Unbounded.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearPMap.closure_smul
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
lemma LinearPMap.closure_smul (U : H →ₗ.[ℂ] H') {c : ℂ} (hc : c ≠ 0) : (c • U).closure = c • U.closure := by
  by_cases h : U.IsClosable
  · apply eq_of_eq_graph
    ext ⟨x₁, x₂⟩
    simp only [← (h.smul c).graph_closure_eq_closure_graph, smul_graph, ← SetLike.mem_coe,
      topologicalClosure_coe, map_coe, LinearMap.prodMap_apply, LinearMap.id_coe, id_eq,
      LinearMap.smul_apply, mem_closure_iff_seq_limit, Set.mem_image, Prod.exists, nhds_prod_eq,
      Filter.tendsto_prod_iff', ← h.graph_closure_eq_closure_graph, Prod.mk.injEq,
      (eq_inv_smul_iff₀ hc).symm, exists_eq_right_right, exists_eq_right]
    constructor <;> intro ⟨b, hb, hb₁, hb₂⟩
    · refine ⟨fun n ↦ ⟨(b n).1, c⁻¹ • (b n).2⟩, fun n ↦ ?_, hb₁, hb₂.const_smul c⁻¹⟩
      obtain ⟨u, v, huv, huv'⟩ := hb n
      have hu := mem_domain_of_mem_graph huv
      use ⟨⟨u, hu⟩, v⟩
      simp [← huv', smul_smul, inv_mul_cancel₀ hc, (image_iff hu).mpr huv]
    · refine ⟨fun n ↦ ⟨(b n).1, c • (b n).2⟩, fun n ↦ ?_, hb₁, ?_⟩
      · obtain ⟨u, hu, hu'⟩ := hb n
        exact ⟨u.1, u.2, by simp_all, by simp [← hu']⟩
      · exact one_smul ℂ x₂ ▸ mul_inv_cancel₀ hc ▸ smul_smul c c⁻¹ x₂ ▸ hb₂.const_smul c
  · rw [closure_def' h, closure_def' <| (not_congr <| IsClosable.smul_iff hc).mpr h]
