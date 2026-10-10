import AFTD.Prelude
import AFTD.Kb.Physics.BiLinearSymm
import AFTD.Kb.Physics.BiLinearSymmInstFun
import AFTD.Kb.Physics.BiLinearSymmSwap
import AFTD.Kb.Physics.BiLinearSymmMapSmul1

/-!
# BiLinearSymm.map_smul₂

Topic: classical_mechanics   Node: b0baf6d3b770

Provenance: formalization of a published result. Source: Physlib, `BiLinearSymm.map_smul₂`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/LinearMaps.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

BiLinearSymm.map_smul₂
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BiLinearSymm in
open BigOperators in
variable {V : Type} [AddCommMonoid V] [Module ℚ V] in
lemma BiLinearSymm.map_smul₂ (f : BiLinearSymm V) (a : ℚ) (S : V) (T : V) : f S (a • T) = a * f S T := by
  rw [f.swap, f.map_smul₁, f.swap]
