import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTSBounded
import AFTD.Kb.Tcs.CslibLTSExampleCountdownLTS
import AFTD.Kb.Tcs.CslibLTSBoundedUpTo
import AFTD.Kb.Tcs.CslibLTSExampleCountdownLTSMTr
import AFTD.Kb.Tcs.CslibLTSMTrNilIff
import AFTD.Kb.Tcs.CslibLTSMTrSingletonIff
import AFTD.Kb.Tcs.CslibLTS

/-!
# Cslib.LTS.Example.countdownLTS_not_bounded

Topic: computability   Node: 670c4b189fdc

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.Example.countdownLTS_not_bounded`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/ExampleTermination.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The countdown LTS is not bounded.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The countdown LTS is not bounded. -/
theorem Cslib.LTS.Example.countdownLTS_not_bounded : ¬ countdownLTS.Bounded := by
  rintro ⟨bound, hbound⟩
  simpa using hbound bound (List.replicate bound ()) 0 (countdownLTS_mTr bound)
