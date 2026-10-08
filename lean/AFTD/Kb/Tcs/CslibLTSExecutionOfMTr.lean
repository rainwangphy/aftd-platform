import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS
import AFTD.Kb.Tcs.CslibLTSMTr
import AFTD.Kb.Tcs.CslibLTSExecution
import AFTD.Kb.Tcs.CslibLTSExecutionRefl
import AFTD.Kb.Tcs.CslibLTSExecutionStepL
import AFTD.Kb.Tcs.CslibLTSMTrNilIff
import AFTD.Kb.Tcs.CslibLTSMTrSingletonIff

/-!
# Cslib.LTS.Execution.of_mTr

Topic: computability   Node: c3fb74f5a0f6

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.Execution.of_mTr`. Lean proof by Fabrizio Montesi, Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Execution.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 adapted; compiled here.

A multistep transition implies the existence of an execution.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.LTS in
variable {State Label : Type*} {lts : LTS State Label} in
/-- A multistep transition implies the existence of an execution. -/
@[grind →]
theorem Cslib.LTS.Execution.of_mTr {lts : LTS State Label}
    {s1 : State} {μs : List Label} {s2 : State}
    (h : lts.MTr s1 μs s2) : ∃ ss : List State, lts.Execution s1 μs s2 ss := by
  induction h
  case refl t =>
    use [t]
    grind
  case stepL t1 μ t2 μs t3 htr hmtr ih =>
    obtain ⟨ss', _⟩ := ih
    use t1 :: ss'
    grind
