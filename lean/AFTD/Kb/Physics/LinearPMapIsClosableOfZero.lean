import AFTD.Prelude

/-!
# LinearPMap.isClosable_of_zero

Topic: quantum_mechanics   Node: b562975ea233

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.isClosable_of_zero`. Lean proof by Adam Bornemann, Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/Unbounded.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A zero LinearPMap (any domain) is closable.
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
/-- A zero LinearPMap (any domain) is closable. -/
lemma LinearPMap.isClosable_of_zero (h_zero : ⇑U = 0) : U.IsClosable := by
  use U.graph.topologicalClosure.toLinearPMap
  refine (toLinearPMap_graph_eq _ fun x hx hx₁ ↦ ?_).symm
  obtain ⟨b, hb, hb'⟩ := mem_closure_iff_seq_limit.mp hx
  have hbn : ∀ n, (b n).snd = 0 := fun n ↦ by specialize hb n; simp_all
  rw [nhds_prod_eq, Filter.tendsto_prod_iff'] at hb'
  simp_all
