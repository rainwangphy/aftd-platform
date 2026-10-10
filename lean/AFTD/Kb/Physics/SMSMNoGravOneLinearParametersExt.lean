import AFTD.Prelude
import AFTD.Kb.Physics.SMSMNoGravOneLinearParameters

/-!
# SM.SMNoGrav.One.linearParameters.ext

Topic: quantum_field_theory   Node: 4c5118356e80

Provenance: formalization of a published result. Source: Physlib, `SM.SMNoGrav.One.linearParameters.ext`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/AnomalyCancellation/NoGrav/One/LinearParameterization.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SM.SMNoGrav.One.linearParameters.ext
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BigOperators in
@[ext]
lemma SM.SMNoGrav.One.linearParameters.ext {S T : linearParameters} (hQ : S.Q' = T.Q') (hY : S.Y = T.Y) (hE : S.E' = T.E') :
    S = T := by
  cases' S
  simp_all only
