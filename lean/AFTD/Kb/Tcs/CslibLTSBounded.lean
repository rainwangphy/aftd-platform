import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS
import AFTD.Kb.Tcs.CslibLTSBoundedUpTo
import AFTD.Kb.Tcs.CslibLTSMTrNilIff
import AFTD.Kb.Tcs.CslibLTSMTrSingletonIff

/-!
# Cslib.LTS.Bounded

Topic: computability   Node: b62775ddb2e1

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.Bounded`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An LTS is bounded if there is a global bound on the length of all of its finite executions.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.LTS in
universe u v in
variable {State : Type u} {Label : Type v} (lts : LTS State Label) in
/-- An LTS is bounded if there is a global bound on the length of all of its finite executions. -/
class Cslib.LTS.Bounded (lts : LTS State Label) where
  bounded : ∃ n, lts.BoundedUpTo n
