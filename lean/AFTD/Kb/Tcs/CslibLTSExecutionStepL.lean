import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS
import AFTD.Kb.Tcs.CslibLTSExecution

/-!
# Cslib.LTS.Execution.stepL

Topic: computability   Node: afa4be19647f

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.Execution.stepL`. Lean proof by Fabrizio Montesi, Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Execution.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Equivalent of `MTr.stepL` for executions.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.LTS in
variable {State Label : Type*} {lts : LTS State Label} in
/-- Equivalent of `MTr.stepL` for executions. -/
theorem Cslib.LTS.Execution.stepL {lts : LTS State Label} (htr : lts.Tr s1 μ s2)
    (hexec : lts.Execution s2 μs s3 ss) : lts.Execution s1 (μ :: μs) s3 (s1 :: ss) := by grind
