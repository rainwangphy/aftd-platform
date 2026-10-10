import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapIsClosedClosureEq
import AFTD.Kb.Physics.StandardModelGaugeGroupIOfU1Subgroup

/-!
# LinearPMap.IsClosed.isClosed_toFun_graph

Topic: quantum_mechanics   Node: 8d2112723631

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.IsClosed.isClosed_toFun_graph`. Lean proof by Adam Bornemann, Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/Unbounded.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearPMap.IsClosed.isClosed_toFun_graph
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
lemma LinearPMap.IsClosed.isClosed_toFun_graph (hU : U.IsClosed) :
    _root_.IsClosed (U.toFun.graph : Set (U.domain × H')) := by
  refine isClosed_of_closure_subset fun ⟨x₁, x₂⟩ hx ↦ ?_
  simp only [SetLike.mem_coe, LinearMap.mem_graph_iff, toFun_eq_coe]
  suffices (↑x₁, x₂) ∈ U.graph.topologicalClosure by
    simp_all [hU.isClosable.graph_closure_eq_closure_graph, hU.closure_eq]
  obtain ⟨b, hb, hbx⟩ := mem_closure_iff_seq_limit.mp hx
  apply mem_closure_iff_seq_limit.mpr
  rw [nhds_prod_eq] at *
  refine ⟨fun n ↦ (↑(b n).1, (b n).2), by simp_all,
    Filter.Tendsto.prodMk (tendsto_subtype_rng.mp hbx.fst) hbx.snd⟩
