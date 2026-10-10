import AFTD.Prelude
import AFTD.Kb.Physics.InnerProductSpaceSubmoduleSubmoduleToLp
import AFTD.Kb.Physics.InnerProductSpaceSubmoduleMemSubmoduleAdjointIffMemSubmoduleToLpOrthogonal
import AFTD.Kb.Physics.InnerProductSpaceSubmoduleSubmoduleToLpClosure

/-!
# InnerProductSpaceSubmodule.mem_submodule_closure_adjoint_iff_mem_submoduleToLp_closure_orthogonal

Topic: classical_mechanics   Node: 3d97329129df

Provenance: formalization of a published result. Source: Physlib, `InnerProductSpaceSubmodule.mem_submodule_closure_adjoint_iff_mem_submoduleToLp_closure_orthogonal`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/InnerProductSpace/Submodule.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

InnerProductSpaceSubmodule.mem_submodule_closure_adjoint_iff_mem_submoduleToLp_closure_orthogonal
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
lemma InnerProductSpaceSubmodule.mem_submodule_closure_adjoint_iff_mem_submoduleToLp_closure_orthogonal :
    g ∈ M.topologicalClosure.adjoint ↔
    WithLp.toLp 2 (g.2, -g.1) ∈ (submoduleToLp M).topologicalClosureᗮ := by
  rw [mem_submodule_adjoint_iff_mem_submoduleToLp_orthogonal, submoduleToLp_closure]
