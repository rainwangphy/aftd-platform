import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS
import AFTD.Kb.Tcs.CslibLTSExecution

/-!
# Cslib.LTS.Execution.cons_invert

Topic: computability   Node: 154fd0859f49

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.Execution.cons_invert`. Lean proof by Fabrizio Montesi, Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Execution.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Deconstruction of executions with `List.cons`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.LTS in
variable {State Label : Type*} {lts : LTS State Label} in
/-- Deconstruction of executions with `List.cons`. -/
theorem Cslib.LTS.Execution.cons_invert (h : lts.Execution s1 (μ :: μs) s2 (s1 :: ss)) :
    lts.Execution (ss[0]'(by grind)) μs s2 ss := by
  obtain ⟨_, _, _, h4⟩ := h
  exists (by grind)
  constructorm* _∧_
  · rfl
  · grind
  · intro k valid
    specialize h4 k <;> grind
