import AFTD.Prelude
import AFTD.Kb.Physics.BiLinearSymm
import AFTD.Kb.Physics.BiLinearSymmInstFun
import AFTD.Kb.Physics.BiLinearSymmToLinear1

/-!
# BiLinearSymm.toLinear₁_apply

Topic: classical_mechanics   Node: 5041a1f6114d

Provenance: formalization of a published result. Source: Physlib, `BiLinearSymm.toLinear₁_apply`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/LinearMaps.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

BiLinearSymm.toLinear₁_apply
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BiLinearSymm in
open BigOperators in
variable {V : Type} [AddCommMonoid V] [Module ℚ V] in
lemma BiLinearSymm.toLinear₁_apply (f : BiLinearSymm V) (S T : V) : f S T = f.toLinear₁ T S := rfl
