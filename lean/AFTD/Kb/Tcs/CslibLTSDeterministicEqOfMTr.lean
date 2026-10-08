import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS
import AFTD.Kb.Tcs.CslibLTSDeterministic
import AFTD.Kb.Tcs.CslibLTSMTr
import AFTD.Kb.Tcs.CslibLTSDeterministicEqOfTr
import AFTD.Kb.Tcs.CslibLTSMTrNilIff
import AFTD.Kb.Tcs.CslibLTSMTrSingletonIff

/-!
# Cslib.LTS.Deterministic.eq_of_mTr

Topic: computability   Node: aa9e10847a57

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.Deterministic.eq_of_mTr`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

In a deterministic lts, multistep transitions with a given start state and trace reach a unique end state.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.LTS in
universe u v in
variable {State : Type u} {Label : Type v} (lts : LTS State Label) in
/-- In a deterministic lts, multistep transitions with a given start state and trace reach a unique end state. -/
theorem Cslib.LTS.Deterministic.eq_of_mTr {lts : LTS State Label} [lts.Deterministic]
    (hmtr : lts.MTr s1 μs s2) (hmtr' : lts.MTr s1 μs s2') : s2 = s2' := by
  induction μs generalizing s1 s2 s2' with
  | nil => grind
  | cons μ μs ih =>
    rcases hmtr with (_ | ⟨htr, hmtr⟩); rcases hmtr' with (_ | ⟨htr', hmtr'⟩)
    rw [eq_of_tr htr htr'] at hmtr
    exact ih hmtr hmtr'
