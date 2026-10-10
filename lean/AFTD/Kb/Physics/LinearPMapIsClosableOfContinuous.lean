import AFTD.Prelude
import AFTD.Kb.Physics.LinearMapContinuousIffBounded

/-!
# LinearPMap.isClosable_of_continuous

Topic: quantum_mechanics   Node: 921c29c4c35a

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.isClosable_of_continuous`. Lean proof by Adam Bornemann, Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/Unbounded.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Continuous operators are closable.
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
/-- Continuous operators are closable. -/
lemma LinearPMap.isClosable_of_continuous (h : Continuous U) : U.IsClosable := by
  use U.graph.topologicalClosure.toLinearPMap
  refine (toLinearPMap_graph_eq _ fun x hx hx₁ ↦ ?_).symm
  obtain ⟨b, hb, hbx⟩ := mem_closure_iff_seq_limit.mp hx
  rw [nhds_prod_eq] at hbx
  refine norm_eq_zero.mp (tendsto_nhds_unique hbx.snd.norm ?_)
  obtain ⟨M, hM, h_bound⟩ := LinearMap.continuous_iff_bounded.mp h
  refine squeeze_zero (g := fun n ↦ M * ‖(b n).1‖) (fun _ ↦ norm_nonneg _) (fun n ↦ ?_) ?_
  · obtain ⟨y, hy₁, hy₂⟩ := (mem_graph_iff _).mp (hb n)
    simp only [← hy₁, ← hy₂]
    exact h_bound y
  · exact mul_zero M ▸ (norm_eq_zero.mpr hx₁) ▸ hbx.fst.norm.const_mul M
