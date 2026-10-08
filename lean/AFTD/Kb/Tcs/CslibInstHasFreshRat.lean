import AFTD.Prelude
import AFTD.Kb.Tcs.CslibHasFresh
import AFTD.Kb.Tcs.CslibHasFreshOfSucc
import AFTD.Kb.Tcs.CslibHasFreshToInfinite
import AFTD.Kb.Tcs.CslibInstHasFreshOfInfinite
import AFTD.Kb.Tcs.CslibInstHasFreshNat
import AFTD.Kb.Tcs.CslibInstHasFreshInt

/-!
# Cslib.instHasFreshRat

Topic: algorithms   Node: d0cc4701462d

Provenance: formalization of a published result. Source: CSLib, `Cslib.instHasFreshRat`. Lean proof by Fabrizio Montesi, Kenny Lau, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/HasFresh.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`ℚ` has a computable fresh function.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u in
/-- `ℚ` has a computable fresh function. -/
instance Cslib.instHasFreshRat : HasFresh ℚ :=
  .ofSucc (· + 1) fun x ↦ lt_add_of_pos_right x one_pos
