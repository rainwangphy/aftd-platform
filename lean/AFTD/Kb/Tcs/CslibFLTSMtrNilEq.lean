import AFTD.Prelude
import AFTD.Kb.Tcs.CslibFLTS
import AFTD.Kb.Tcs.CslibFLTSMtr

/-!
# Cslib.FLTS.mtr_nil_eq

Topic: computability   Node: a8cbcd0ebef7

Provenance: formalization of a published result. Source: CSLib, `Cslib.FLTS.mtr_nil_eq`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/FLTS/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.FLTS.mtr_nil_eq
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {State Label : Type*} in
@[simp, scoped grind =]
theorem Cslib.FLTS.mtr_nil_eq {flts : FLTS State Label} {s : State} : flts.mtr s [] = s := rfl
