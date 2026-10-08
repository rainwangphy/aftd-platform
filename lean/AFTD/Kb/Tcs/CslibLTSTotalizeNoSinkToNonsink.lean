import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS
import AFTD.Kb.Tcs.CslibLTSMTr
import AFTD.Kb.Tcs.CslibLTSTotalize
import AFTD.Kb.Tcs.CslibLTSMTrNilIff
import AFTD.Kb.Tcs.CslibLTSMTrSingletonIff
import AFTD.Kb.Tcs.CslibLTSInstTotalOptionTotalize

/-!
# Cslib.LTS.totalize.no_sink_to_nonsink

Topic: computability   Node: ef91f97c7294

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.totalize.no_sink_to_nonsink`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Total.lean (Copyright (c) 2026 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

In `totalize`, there is no finite execution from the sink state to any non-sink state.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.LTS in
variable {State Label : Type*} {lts : LTS State Label} in
set_option linter.tacticAnalysis.verifyGrindOnly false in
/-- In `totalize`, there is no finite execution from the sink state to any non-sink state. -/
theorem Cslib.LTS.totalize.no_sink_to_nonsink {μs : List Label} {t : State} :
    ¬ lts.totalize.MTr (none) μs (some t) := by
  intro h
  generalize h_s : (none : Option State) = s'
  generalize h_t : (some t : Option State) = t'
  rw [h_s, h_t] at h
  induction h
  · grind
  · grind only [totalize]
