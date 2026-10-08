import AFTD.Prelude
import AFTD.Kb.Tcs.CslibFLTS
import AFTD.Kb.Tcs.CslibLTS
import AFTD.Kb.Tcs.CslibFLTSToLTS
import AFTD.Kb.Tcs.CslibFLTSInstCoeLTS

/-!
# Cslib.FLTS.toLTS_tr

Topic: computability   Node: 5ebc2f1afb5b

Provenance: formalization of a published result. Source: CSLib, `Cslib.FLTS.toLTS_tr`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/FLTS/FLTSToLTS.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`FLTS.toLTS` correctly characterises transitions.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {State Label : Type*} in
/-- `FLTS.toLTS` correctly characterises transitions. -/
@[scoped grind =]
theorem Cslib.FLTS.toLTS_tr {flts : FLTS State Label} {s1 : State} {μ : Label} {s2 : State} :
  flts.toLTS.Tr s1 μ s2 ↔ flts.tr s1 μ = s2 := by rfl
