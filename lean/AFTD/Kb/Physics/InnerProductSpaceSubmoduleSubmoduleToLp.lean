import AFTD.Prelude

/-!
# InnerProductSpaceSubmodule.submoduleToLp

Topic: classical_mechanics   Node: c88e0b5a0388

Provenance: formalization of a published result. Source: Physlib, `InnerProductSpaceSubmodule.submoduleToLp`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/InnerProductSpace/Submodule.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The submodule of `WithLp 2 (E × F)` defined by `M`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap Submodule in
variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  (M : Submodule ℂ (E × F))
  (f : E × F) (g : F × E) in
/-- The submodule of `WithLp 2 (E × F)` defined by `M`. -/
def InnerProductSpaceSubmodule.submoduleToLp : Submodule ℂ (WithLp 2 (E × F)) where
  carrier := {x | x.ofLp ∈ M}
  add_mem' := by
    intro a b ha hb
    exact Submodule.add_mem M ha hb
  zero_mem' := Submodule.zero_mem M
  smul_mem' := by
    intro c x hx
    exact Submodule.smul_mem M c hx
