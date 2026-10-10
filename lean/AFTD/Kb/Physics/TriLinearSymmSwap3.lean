import AFTD.Prelude
import AFTD.Kb.Physics.TriLinearSymm
import AFTD.Kb.Physics.TriLinearSymmInstFun
import AFTD.Kb.Physics.TriLinearSymmSwap1
import AFTD.Kb.Physics.TriLinearSymmSwap2

/-!
# TriLinearSymm.swap₃

Topic: classical_mechanics   Node: 28020b6ea97c

Provenance: formalization of a published result. Source: Physlib, `TriLinearSymm.swap₃`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/LinearMaps.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

TriLinearSymm.swap₃
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open TriLinearSymm in
open BigOperators in
variable {V : Type} [AddCommMonoid V] [Module ℚ V] in
lemma TriLinearSymm.swap₃ (f : TriLinearSymm V) (S T L : V) : f S T L = f L T S := by
  rw [f.swap₁, f.swap₂, f.swap₁]
