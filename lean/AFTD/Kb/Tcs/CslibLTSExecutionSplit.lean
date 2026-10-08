import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS
import AFTD.Kb.Tcs.CslibLTSExecution

/-!
# Cslib.LTS.Execution.split

Topic: computability   Node: c4e2abdd640f

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.Execution.split`. Lean proof by Fabrizio Montesi, Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Execution.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An execution can be split at any intermediate state into two executions.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.LTS in
variable {State Label : Type*} {lts : LTS State Label} in
/-- An execution can be split at any intermediate state into two executions. -/
theorem Cslib.LTS.Execution.split
    {lts : LTS State Label} {s t : State} {μs : List Label} {ss : List State}
    (he : lts.Execution s μs t ss) (n : ℕ) (hn : n ≤ μs.length) :
    lts.Execution s (μs.take n) (ss[n]'(by grind)) (ss.take (n + 1)) ∧
    lts.Execution (ss[n]'(by grind)) (μs.drop n) t (ss.drop n) := by
  have : n + (ss.length - n - 1) = ss.length - 1 := by grind
  simp [Execution]
  grind
