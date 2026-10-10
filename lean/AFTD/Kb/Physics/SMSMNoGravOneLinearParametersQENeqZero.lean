import AFTD.Prelude

/-!
# SM.SMNoGrav.One.linearParametersQENeqZero

Topic: quantum_field_theory   Node: c689caadaccb

Provenance: formalization of a published result. Source: Physlib, `SM.SMNoGrav.One.linearParametersQENeqZero`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/AnomalyCancellation/NoGrav/One/LinearParameterization.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The parameters for solutions to the linear ACCs with the condition that Q and E are non-zero.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BigOperators in
/-- The parameters for solutions to the linear ACCs with the condition that Q and E are non-zero. -/
structure SM.SMNoGrav.One.linearParametersQENeqZero where
  /-- The parameter `x`. -/
  x : ℚ
  /-- The parameter `v`. -/
  v : ℚ
  /-- The parameter `w`. -/
  w : ℚ
  hx : x ≠ 0
  hvw : v + w ≠ 0
