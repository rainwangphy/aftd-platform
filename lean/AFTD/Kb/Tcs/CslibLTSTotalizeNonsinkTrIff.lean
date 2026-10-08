import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS
import AFTD.Kb.Tcs.CslibLTSTotalize
import AFTD.Kb.Tcs.CslibLTSInstTotalOptionTotalize

/-!
# Cslib.LTS.totalize.nonsink_tr_iff

Topic: computability   Node: 1b3ddae6c574

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.totalize.nonsink_tr_iff`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Total.lean (Copyright (c) 2026 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

In `totalize`, the transitions between non-sink states correspond exactly to the transitions in the original LTS.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.LTS in
variable {State Label : Type*} {lts : LTS State Label} in
/-- In `totalize`, the transitions between non-sink states correspond exactly to the transitions in the original LTS. -/
@[simp]
theorem Cslib.LTS.totalize.nonsink_tr_iff {μ : Label} {s t : State} :
    lts.totalize.Tr (some s) μ (some t) ↔ lts.Tr s μ t := by
  simp [totalize]
