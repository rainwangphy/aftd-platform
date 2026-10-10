import AFTD.Prelude

/-!
# Function.HasTemperateGrowth.prod

Topic: classical_mechanics   Node: cabcd009b86d

Provenance: formalization of a published result. Source: Physlib, `Function.HasTemperateGrowth.prod`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/HasTemperateGrowth.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The finite product of functions of temperate growth is again of temperate growth.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
/-- The finite product of functions of temperate growth is again of temperate growth. -/
@[to_fun (attr := fun_prop)]
lemma Function.HasTemperateGrowth.prod {ι : Type*} {s : Finset ι} {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedCommRing F] [NormedAlgebra ℝ F] {f : ι → E → F}
    (hf : ∀ i ∈ s, HasTemperateGrowth (f i)) : HasTemperateGrowth (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact const _
  | insert j t hjt ih =>
    simp_rw [insert_eq, prod_union (disjoint_singleton_left.mpr hjt), prod_singleton]
    exact fun_mul (hf j <| mem_insert_self j t) (ih fun i h ↦ hf i <| mem_insert_of_mem h)
