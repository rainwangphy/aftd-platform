import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS
import AFTD.Kb.Tcs.CslibLTSExecution

/-!
# Cslib.LTS.Execution.nonEmpty_states

Topic: computability   Node: 5c8da52e7b92

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.Execution.nonEmpty_states`. Lean proof by Fabrizio Montesi, Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Execution.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Every execution has at least one intermediate state.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.LTS in
variable {State Label : Type*} {lts : LTS State Label} in
/-- Every execution has at least one intermediate state. -/
@[grind →]
theorem Cslib.LTS.Execution.nonEmpty_states (h : lts.Execution s1 μs s2 ss) :
    ss ≠ [] := by grind
