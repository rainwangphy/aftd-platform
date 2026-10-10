import AFTD.Prelude
import AFTD.Kb.Physics.BiLinearSymm
import AFTD.Kb.Physics.BiLinearSymmInstFun

/-!
# BiLinearSymm.map_add₁

Topic: classical_mechanics   Node: ac124e69b9c6

Provenance: formalization of a published result. Source: Physlib, `BiLinearSymm.map_add₁`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/LinearMaps.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

BiLinearSymm.map_add₁
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BiLinearSymm in
open BigOperators in
variable {V : Type} [AddCommMonoid V] [Module ℚ V] in
lemma BiLinearSymm.map_add₁ (f : BiLinearSymm V) (S1 S2 T : V) : f (S1 + S2) T = f S1 T + f S2 T := by
  have h : f (S1 + S2) = f S1 + f S2 := by
    exact f.map_add S1 S2
  simp [h]
