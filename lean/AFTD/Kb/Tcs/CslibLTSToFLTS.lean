import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS
import AFTD.Kb.Tcs.CslibFLTS
import AFTD.Kb.Tcs.CslibLTSSetImage
import AFTD.Kb.Tcs.CslibFLTSMtrNilEq
import AFTD.Kb.Tcs.CslibFLTSMtrConcatEq

/-!
# Cslib.LTS.toFLTS

Topic: computability   Node: bc4c8258be2a

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.toFLTS`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/FLTS/LTSToFLTS.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Converts an `LTS` into an `FLTS` using the subset construction.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.LTS in
variable {State Label : Type*} in
/-- Converts an `LTS` into an `FLTS` using the subset construction. -/
@[grind =]
def Cslib.LTS.toFLTS (lts : LTS State Label) : FLTS (Set State) Label where
  tr := lts.setImage
