import AFTD.Prelude
import AFTD.Kb.Physics.BiLinearSymm
import AFTD.Kb.Physics.HomogeneousQuadratic
import AFTD.Kb.Physics.HomogeneousQuadraticInstFun
import AFTD.Kb.Physics.BiLinearSymmToHomogeneousQuad
import AFTD.Kb.Physics.BiLinearSymmInstFun
import AFTD.Kb.Physics.BiLinearSymmMapAdd1
import AFTD.Kb.Physics.BiLinearSymmSwap

/-!
# BiLinearSymm.toHomogeneousQuad_add

Topic: classical_mechanics   Node: 2be0194ac990

Provenance: formalization of a published result. Source: Physlib, `BiLinearSymm.toHomogeneousQuad_add`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/LinearMaps.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

BiLinearSymm.toHomogeneousQuad_add
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BiLinearSymm in
open BigOperators in
variable {V : Type} [AddCommMonoid V] [Module ℚ V] in
set_option backward.isDefEq.respectTransparency false in
lemma BiLinearSymm.toHomogeneousQuad_add {V : Type} [AddCommMonoid V] [Module ℚ V]
    (τ : BiLinearSymm V) (S T : V) :
    τ.toHomogeneousQuad (S + T) = τ.toHomogeneousQuad S +
    τ.toHomogeneousQuad T + 2 * τ S T := by
  simp only [HomogeneousQuadratic, toHomogeneousQuad_apply, τ.map_add₁, map_add, τ.swap T S]
  grind
