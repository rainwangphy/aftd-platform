import AFTD.Prelude
import AFTD.Kb.Tcs.CslibFLTS
import AFTD.Kb.Tcs.CslibLTS
import AFTD.Kb.Tcs.CslibFLTSToLTS

/-!
# Cslib.FLTS.instCoeLTS

Topic: computability   Node: a56263d4b984

Provenance: formalization of a published result. Source: CSLib, `Cslib.FLTS.instCoeLTS`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/FLTS/FLTSToLTS.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.FLTS.instCoeLTS
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {State Label : Type*} in
instance Cslib.FLTS.instCoeLTS : Coe (FLTS State Label) (LTS State Label) where
  coe := toLTS
