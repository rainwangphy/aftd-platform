import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapIsLowerBound

/-!
# LinearPMap.isLowerBound_closure

Topic: quantum_mechanics   Node: 3325d7c620df

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.isLowerBound_closure`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/SpectralTheory/Basic.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearPMap.isLowerBound_closure
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
open Submodule in
open Metric in
open InnerProductSpace in
open Complex in
open ComplexConjugate in
open Set in
open Pointwise in
lemma LinearPMap.isLowerBound_closure
    {T : H →ₗ.[ℂ] H} {z : ℂ} {c : ℝ} (h : IsLowerBound T z c) : IsLowerBound T.closure z c := by
  by_cases hT : T.IsClosable
  · intro x
    obtain ⟨b, hb, hb'⟩ := mem_closure_iff_seq_limit.mp <|
      hT.graph_closure_eq_closure_graph ▸ T.closure.mem_graph x
    rw [nhds_prod_eq] at hb'
    refine le_of_tendsto_of_tendsto' (hb'.fst.norm.const_mul c)
      ((hb'.snd.sub <| hb'.fst.const_smul z).norm) fun n ↦ ?_
    obtain ⟨y, hy₁, hy₂⟩ := (mem_graph_iff _).mp (hb n)
    exact hy₁ ▸ hy₂ ▸ h y
  · rwa [closure_def' hT]
