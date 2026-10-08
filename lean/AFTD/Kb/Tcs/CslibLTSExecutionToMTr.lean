import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS
import AFTD.Kb.Tcs.CslibLTSExecution
import AFTD.Kb.Tcs.CslibLTSMTr
import AFTD.Kb.Tcs.CslibLTSExecutionConsInvert
import AFTD.Kb.Tcs.CslibLTSMTrNilIff
import AFTD.Kb.Tcs.CslibLTSMTrSingletonIff

/-!
# Cslib.LTS.Execution.to_mTr

Topic: computability   Node: 1e775bdb6285

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.Execution.to_mTr`. Lean proof by Fabrizio Montesi, Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Execution.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Converts an execution into a multistep transition.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.LTS in
variable {State Label : Type*} {lts : LTS State Label} in
/-- Converts an execution into a multistep transition. -/
@[grind →]
theorem Cslib.LTS.Execution.to_mTr (hexec : lts.Execution s1 μs s2 ss) :
    lts.MTr s1 μs s2 := by
  induction ss generalizing s1 μs
  case nil => grind
  case cons s1' ss ih =>
    let ⟨hlen, hstart, hfinal, hexec'⟩ := hexec
    have : s1' = s1 := by grind
    rw [this] at hexec' hexec
    cases μs
    · grind
    case cons μ μs =>
      specialize ih (s1 := ss[0]'(by grind)) (μs := μs)
      apply Execution.cons_invert at hexec
      apply MTr.stepL
      · have : lts.Tr s1 μ (ss[0]'(by grind)) := by grind
        apply this
      · grind
