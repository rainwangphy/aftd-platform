import AFTD.Prelude

/-!
# LinearPMap.zero_smul_le

Topic: classical_mechanics   Node: 41de628b17de

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.zero_smul_le`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/LinearPMap.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearPMap.zero_smul_le
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Submodule in
variable {R : Type*} [Ring R] in
variable {E : Type*} [AddCommGroup E] [Module R E] in
variable {F : Type*} [AddCommGroup F] [Module R F] in
variable {𝕜 : Type*} [Field 𝕜] [Module 𝕜 E] [Module 𝕜 F] in
lemma LinearPMap.zero_smul_le (f : E →ₗ.[𝕜] F) : (0 : 𝕜) • f ≤ 0 := ⟨le_top, by simp⟩
