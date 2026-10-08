import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTSTerminating
import AFTD.Kb.Tcs.CslibLTSExampleCountdownLTS
import AFTD.Kb.Tcs.CslibLTSUnlabelledTr
import AFTD.Kb.Tcs.CslibLTS

/-!
# Cslib.LTS.Example.countdownLTS_terminating

Topic: computability   Node: 725bcdc446eb

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.Example.countdownLTS_terminating`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/ExampleTermination.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.LTS.Example.countdownLTS_terminating
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
instance Cslib.LTS.Example.countdownLTS_terminating : countdownLTS.Terminating where
  terminating := by
    apply Subrelation.wf _ Nat.lt_wfRel.wf
    rintro s2 s1 ⟨_, rfl⟩
    exact Nat.lt_succ_self s2
