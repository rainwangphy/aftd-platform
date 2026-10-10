import AFTD.Prelude
import AFTD.Kb.Physics.TriLinearSymm
import AFTD.Kb.Physics.TriLinearSymmInstFun
import AFTD.Kb.Physics.TriLinearSymmSwap3
import AFTD.Kb.Physics.TriLinearSymmMapAdd1

/-!
# TriLinearSymm.map_add₃

Topic: classical_mechanics   Node: 5432ed8699ce

Provenance: formalization of a published result. Source: Physlib, `TriLinearSymm.map_add₃`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/LinearMaps.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

TriLinearSymm.map_add₃
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open TriLinearSymm in
open BigOperators in
variable {V : Type} [AddCommMonoid V] [Module ℚ V] in
lemma TriLinearSymm.map_add₃ (f : TriLinearSymm V) (S T L1 L2 : V) :
    f S T (L1 + L2) = f S T L1 + f S T L2 := by
  rw [f.swap₃, f.map_add₁, f.swap₃, f.swap₃ L2 T S]
