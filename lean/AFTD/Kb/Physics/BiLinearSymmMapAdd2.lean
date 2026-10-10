import AFTD.Prelude
import AFTD.Kb.Physics.BiLinearSymm
import AFTD.Kb.Physics.BiLinearSymmInstFun
import AFTD.Kb.Physics.BiLinearSymmSwap
import AFTD.Kb.Physics.BiLinearSymmMapAdd1

/-!
# BiLinearSymm.map_add₂

Topic: classical_mechanics   Node: 760462fde4e1

Provenance: formalization of a published result. Source: Physlib, `BiLinearSymm.map_add₂`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/LinearMaps.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

BiLinearSymm.map_add₂
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BiLinearSymm in
open BigOperators in
variable {V : Type} [AddCommMonoid V] [Module ℚ V] in
lemma BiLinearSymm.map_add₂ (f : BiLinearSymm V) (S : V) (T1 T2 : V) :
    f S (T1 + T2) = f S T1 + f S T2 := by
  rw [f.swap, f.map_add₁, f.swap T1 S, f.swap T2 S]
