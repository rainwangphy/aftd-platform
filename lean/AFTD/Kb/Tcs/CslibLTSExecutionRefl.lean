import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS
import AFTD.Kb.Tcs.CslibLTSExecution

/-!
# Cslib.LTS.Execution.refl

Topic: computability   Node: ce0ef0408b0a

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.Execution.refl`. Lean proof by Fabrizio Montesi, Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Execution.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Every state has an execution of zero steps terminating in itself.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.LTS in
variable {State Label : Type*} {lts : LTS State Label} in
/-- Every state has an execution of zero steps terminating in itself. -/
@[grind ⇒]
theorem Cslib.LTS.Execution.refl (lts : LTS State Label) (s : State) : lts.Execution s [] s [s] := by
  grind
