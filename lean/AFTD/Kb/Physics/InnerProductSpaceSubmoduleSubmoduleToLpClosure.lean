import AFTD.Prelude
import AFTD.Kb.Physics.InnerProductSpaceSubmoduleSubmoduleToLp
import AFTD.Kb.Physics.InnerProductSpaceSubmoduleMemSubmoduleIffMemSubmoduleToLp

/-!
# InnerProductSpaceSubmodule.submoduleToLp_closure

Topic: classical_mechanics   Node: 9487c03895c1

Provenance: formalization of a published result. Source: Physlib, `InnerProductSpaceSubmodule.submoduleToLp_closure`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/InnerProductSpace/Submodule.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

InnerProductSpaceSubmodule.submoduleToLp_closure
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open InnerProductSpaceSubmodule in
open LinearPMap Submodule in
variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  (M : Submodule ℂ (E × F))
  (f : E × F) (g : F × E) in
lemma InnerProductSpaceSubmodule.submoduleToLp_closure :
    (submoduleToLp M.topologicalClosure) = (submoduleToLp M).topologicalClosure := by
  rw [Submodule.ext_iff]
  intro x
  rw [← mem_submodule_iff_mem_submoduleToLp]
  change x.ofLp ∈ _root_.closure M ↔ x ∈ _root_.closure (submoduleToLp M)
  repeat rw [mem_closure_iff_nhds]
  constructor
  · intro h t ht
    apply mem_nhds_iff.mp at ht
    rcases ht with ⟨t1, ht1, ht1', hx⟩
    have : ∃ t' ∈ nhds x.ofLp, (∀ y ∈ t', WithLp.toLp 2 y ∈ t1) := by
      refine Filter.eventually_iff_exists_mem.mp ?_
      apply ContinuousAt.eventually_mem (by fun_prop) (IsOpen.mem_nhds ht1' hx)
    rcases this with ⟨t2, ht2, ht2'⟩
    rcases h t2 ht2 with ⟨w, hw⟩
    use WithLp.toLp 2 w
    exact ⟨Set.mem_preimage.mp (ht1 (ht2' w hw.1)),
      (mem_submodule_iff_mem_submoduleToLp M w).mpr hw.2⟩
  · intro h t ht
    apply mem_nhds_iff.mp at ht
    rcases ht with ⟨t1, ht1, ht1', hx⟩
    have : ∃ t' ∈ nhds x, (∀ y ∈ t', y.ofLp ∈ t1) := by
      refine Filter.eventually_iff_exists_mem.mp ?_
      exact ContinuousAt.eventually_mem (by fun_prop) (IsOpen.mem_nhds ht1' hx)
    rcases this with ⟨t2, ht2, ht2'⟩
    rcases h t2 ht2 with ⟨w, hw⟩
    use w.ofLp
    exact ⟨Set.mem_preimage.mp (ht1 (ht2' w hw.1)), (mem_toAddSubgroup (submoduleToLp M)).mp hw.2⟩
