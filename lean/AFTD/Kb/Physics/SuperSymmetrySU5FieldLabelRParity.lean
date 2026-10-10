import AFTD.Prelude
import AFTD.Kb.Physics.SuperSymmetrySU5FieldLabel
import AFTD.Kb.Physics.SuperSymmetrySU5InstFintypeFieldLabel
import AFTD.Kb.GameTheoryEconomics.GameTreeIsZeroSum

/-!
# SuperSymmetry.SU5.FieldLabel.RParity

Topic: quantum_field_theory   Node: cc680ce64e0f

Provenance: formalization of a published result. Source: Physlib, `SuperSymmetry.SU5.FieldLabel.RParity`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/SU5/FieldLabels.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The R-Parity of a field, landing on `1` if it is in the non-trivial representation and `0` otherwise.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The R-Parity of a field, landing on `1` if it is in the non-trivial representation and `0` otherwise. -/
def SuperSymmetry.SU5.FieldLabel.RParity : FieldLabel → Fin 2
  | fiveBarHu => 0
  | fiveHu => 0
  | fiveBarHd => 0
  | fiveHd => 0
  | fiveBarMatter => 1
  | fiveMatter => 1
  | tenMatter => 1
