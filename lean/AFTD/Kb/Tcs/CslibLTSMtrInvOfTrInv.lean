import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS
import AFTD.Kb.Tcs.CslibLTSTrInv
import AFTD.Kb.Tcs.CslibLTSMTrInv
import AFTD.Kb.Tcs.CslibLTSMTr
import AFTD.Kb.Tcs.CslibLTSMTrNilIff
import AFTD.Kb.Tcs.CslibLTSMTrSingletonIff

/-!
# Cslib.LTS.mtrInv_of_trInv

Topic: computability   Node: 3a0d9b46cb68

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.mtrInv_of_trInv`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Any single-step invariant is also a multistep invariant.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.LTS in
universe u v in
variable {State : Type u} {Label : Type v} (lts : LTS State Label) in
/-- Any single-step invariant is also a multistep invariant. -/
theorem Cslib.LTS.mtrInv_of_trInv {lts : LTS State Label} {p : State → Prop}
    (htr : lts.TrInv p) : lts.MTrInv p := by
  intro s1 μs s2 h
  induction h <;> grind
