import AFTD.Prelude
import AFTD.Kb.Tcs.CslibHasFresh
import AFTD.Kb.Tcs.CslibHasFreshOfSucc
import AFTD.Kb.Tcs.CslibHasFreshToInfinite
import AFTD.Kb.Tcs.CslibInstHasFreshOfInfinite
import AFTD.Kb.Tcs.CslibInstHasFreshNat

/-!
# Cslib.instHasFreshInt

Topic: algorithms   Node: 74365f5ab8cb

Provenance: formalization of a published result. Source: CSLib, `Cslib.instHasFreshInt`. Lean proof by Fabrizio Montesi, Kenny Lau, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/HasFresh.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`ℤ` has a computable fresh function.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u in
/-- `ℤ` has a computable fresh function. -/
instance Cslib.instHasFreshInt : HasFresh ℤ :=
  .ofSucc (· + 1) Int.lt_succ
