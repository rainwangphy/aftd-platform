import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTSMTr
import AFTD.Kb.Tcs.CslibLTSExampleCountdownLTS
import AFTD.Kb.Tcs.CslibLTSMTrNilIff
import AFTD.Kb.Tcs.CslibLTSMTrSingletonIff
import AFTD.Kb.Tcs.CslibLTS

/-!
# Cslib.LTS.Example.countdownLTS_mTr

Topic: computability   Node: 36cfc8fd0034

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.Example.countdownLTS_mTr`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/ExampleTermination.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.LTS.Example.countdownLTS_mTr
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
theorem Cslib.LTS.Example.countdownLTS_mTr (n : ℕ) :
    countdownLTS.MTr n (List.replicate n ()) 0 := by
  induction n with
  | zero => exact .refl
  | succ n ih =>
      simpa [List.replicate_succ] using MTr.stepL (by simp [countdownLTS]) ih
