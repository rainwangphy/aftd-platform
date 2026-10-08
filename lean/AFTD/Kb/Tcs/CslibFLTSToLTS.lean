import AFTD.Prelude
import AFTD.Kb.Tcs.CslibFLTS
import AFTD.Kb.Tcs.CslibLTS

/-!
# Cslib.FLTS.toLTS

Topic: computability   Node: 79d7e2689b31

Provenance: formalization of a published result. Source: CSLib, `Cslib.FLTS.toLTS`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/FLTS/FLTSToLTS.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`FLTS` is a special case of `LTS`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {State Label : Type*} in
/-- `FLTS` is a special case of `LTS`. -/
@[scoped grind =]
def Cslib.FLTS.toLTS (flts : FLTS State Label) : LTS State Label where
  Tr s1 μ s2 := flts.tr s1 μ = s2
