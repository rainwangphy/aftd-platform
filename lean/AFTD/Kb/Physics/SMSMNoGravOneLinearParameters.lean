import AFTD.Prelude

/-!
# SM.SMNoGrav.One.linearParameters

Topic: quantum_field_theory   Node: f03bea7d4346

Provenance: formalization of a published result. Source: Physlib, `SM.SMNoGrav.One.linearParameters`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/AnomalyCancellation/NoGrav/One/LinearParameterization.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The parameters for a linear parameterization to the solution of the linear ACCs.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BigOperators in
/-- The parameters for a linear parameterization to the solution of the linear ACCs. -/
structure SM.SMNoGrav.One.linearParameters where
  /-- The parameter `Q'`. -/
  Q' : ℚ
  /-- The parameter `Y`. -/
  Y : ℚ
  /-- The parameter `E'`. -/
  E' : ℚ
