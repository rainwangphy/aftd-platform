import AFTD.Prelude
import AFTD.Kb.Physics.TriLinearSymm
import AFTD.Kb.Physics.TriLinearSymmInstFun
import AFTD.Kb.Physics.TriLinearSymmSwap1
import AFTD.Kb.Physics.TriLinearSymmMapSmul1

/-!
# TriLinearSymm.map_smul₂

Topic: classical_mechanics   Node: 9748facdd99e

Provenance: formalization of a published result. Source: Physlib, `TriLinearSymm.map_smul₂`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/LinearMaps.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

TriLinearSymm.map_smul₂
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open TriLinearSymm in
open BigOperators in
variable {V : Type} [AddCommMonoid V] [Module ℚ V] in
lemma TriLinearSymm.map_smul₂ (f : TriLinearSymm V) (S : V) (a : ℚ) (T L : V) :
    f S (a • T) L = a * f S T L := by
  rw [f.swap₁, f.map_smul₁, f.swap₁]
