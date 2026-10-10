import AFTD.Prelude
import AFTD.Kb.Physics.TriLinearSymm
import AFTD.Kb.Physics.TriLinearSymmInstFun
import AFTD.Kb.Physics.TriLinearSymmSwap1
import AFTD.Kb.Physics.TriLinearSymmMapAdd1

/-!
# TriLinearSymm.map_add₂

Topic: classical_mechanics   Node: 9f5b394e0e99

Provenance: formalization of a published result. Source: Physlib, `TriLinearSymm.map_add₂`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/LinearMaps.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

TriLinearSymm.map_add₂
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open TriLinearSymm in
open BigOperators in
variable {V : Type} [AddCommMonoid V] [Module ℚ V] in
lemma TriLinearSymm.map_add₂ (f : TriLinearSymm V) (S T1 T2 L : V) :
    f S (T1 + T2) L = f S T1 L + f S T2 L := by
  rw [f.swap₁, f.map_add₁, f.swap₁ S T1, f.swap₁ S T2]
