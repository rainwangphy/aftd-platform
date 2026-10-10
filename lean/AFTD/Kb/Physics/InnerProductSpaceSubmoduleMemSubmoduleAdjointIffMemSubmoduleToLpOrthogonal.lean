import AFTD.Prelude
import AFTD.Kb.Physics.InnerProductSpaceSubmoduleSubmoduleToLp
import AFTD.Kb.Physics.InnerProductSpaceSubmoduleMemSubmoduleIffMemSubmoduleToLp

/-!
# InnerProductSpaceSubmodule.mem_submodule_adjoint_iff_mem_submoduleToLp_orthogonal

Topic: classical_mechanics   Node: cce35eb1b9f2

Provenance: formalization of a published result. Source: Physlib, `InnerProductSpaceSubmodule.mem_submodule_adjoint_iff_mem_submoduleToLp_orthogonal`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/InnerProductSpace/Submodule.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

InnerProductSpaceSubmodule.mem_submodule_adjoint_iff_mem_submoduleToLp_orthogonal
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
lemma InnerProductSpaceSubmodule.mem_submodule_adjoint_iff_mem_submoduleToLp_orthogonal :
    g ∈ M.adjoint ↔ WithLp.toLp 2 (g.2, -g.1) ∈ (submoduleToLp M)ᗮ := by
  constructor <;> intro h
  · rw [mem_orthogonal]
    intro u hu
    rw [mem_adjoint_iff] at h
    have h' : inner ℂ u.snd g.1 = inner ℂ u.fst g.2 := by
      rw [← sub_eq_zero]
      exact h u.fst u.snd hu
    simp [h']
  · rw [mem_adjoint_iff]
    intro a b hab
    rw [mem_orthogonal] at h
    have hab' := (mem_submodule_iff_mem_submoduleToLp M (a, b)).mp hab
    have h' : inner ℂ a g.2 = inner ℂ b g.1 := by
      rw [← sub_eq_zero, sub_eq_add_neg, ← inner_neg_right]
      exact h (WithLp.toLp 2 (a, b)) hab'
    simp [h']
