import AFTD.Prelude
import AFTD.Kb.Physics.TimeUnit
import AFTD.Kb.Physics.InstPositiveRealUnitCoreTimeUnit

/-!
# TimeUnit.seconds

Topic: classical_mechanics   Node: 9be520f4cbc1

Provenance: formalization of a published result. Source: Physlib, `TimeUnit.seconds`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Time/TimeUnit.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The definition of a time unit of seconds.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open NNReal in
open NNReal in
/-- The definition of a time unit of seconds. -/
def TimeUnit.seconds : TimeUnit := ⟨1, by norm_num⟩
