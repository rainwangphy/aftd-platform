import AFTD.Prelude
import AFTD.Kb.Physics.InnerProductSpaceSubmoduleSubmoduleToLp
import AFTD.Kb.Physics.InnerProductSpaceSubmoduleMemSubmoduleIffMemSubmoduleToLp

/-!
# InnerProductSpaceSubmodule.mem_submodule_adjoint_adjoint_iff_mem_submoduleToLp_orthogonal_orthogonal

Topic: classical_mechanics   Node: 655dd90e68eb

Provenance: formalization of a published result. Source: Physlib, `InnerProductSpaceSubmodule.mem_submodule_adjoint_adjoint_iff_mem_submoduleToLp_orthogonal_orthogonal`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/InnerProductSpace/Submodule.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

InnerProductSpaceSubmodule.mem_submodule_adjoint_adjoint_iff_mem_submoduleToLp_orthogonal_orthogonal
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
lemma InnerProductSpaceSubmodule.mem_submodule_adjoint_adjoint_iff_mem_submoduleToLp_orthogonal_orthogonal :
    f ∈ M.adjoint.adjoint ↔ WithLp.toLp 2 f ∈ (submoduleToLp M)ᗮᗮ := by
  simp only [mem_adjoint_iff]
  trans ∀ v, (∀ w ∈ submoduleToLp M, inner ℂ w v = 0) → inner ℂ v (WithLp.toLp 2 f) = 0
  · constructor <;> intro h
    · intro v hw
      have h' := h (-v.snd) v.fst
      rw [inner_neg_left, sub_neg_eq_add] at h'
      apply h'
      intro a b hab
      rw [inner_neg_right, neg_sub_left, neg_eq_zero]
      exact hw (WithLp.toLp 2 (a, b)) ((mem_submodule_iff_mem_submoduleToLp M (a, b)).mp hab)
    · intro a b h'
      rw [sub_eq_add_neg, ← inner_neg_left]
      apply h (WithLp.toLp 2 (b, -a))
      intro w hw
      have hw' := h' w.fst w.snd hw
      rw [sub_eq_zero] at hw'
      simp [hw']
  simp only [← mem_orthogonal]
