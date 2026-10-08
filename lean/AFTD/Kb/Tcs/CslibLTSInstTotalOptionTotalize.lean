import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS
import AFTD.Kb.Tcs.CslibLTSTotal
import AFTD.Kb.Tcs.CslibLTSTotalize

/-!
# Cslib.LTS.instTotalOptionTotalize

Topic: computability   Node: 5036dc835459

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.instTotalOptionTotalize`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Total.lean (Copyright (c) 2026 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The LTS constructed by `totalize` is indeed total.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.LTS in
variable {State Label : Type*} {lts : LTS State Label} in
/-- The LTS constructed by `totalize` is indeed total. -/
instance Cslib.LTS.instTotalOptionTotalize (lts : LTS State Label) : lts.totalize.Total where
  total _ _ := by
    use none
    simp [totalize]
