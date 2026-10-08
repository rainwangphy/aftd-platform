import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS
import AFTD.Kb.Tcs.CslibLTSImageFinite
import AFTD.Kb.Tcs.CslibLTSImage

/-!
# Cslib.LTS.finiteState_imageFinite

Topic: computability   Node: 22fc92af7331

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.finiteState_imageFinite`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Every finite-state LTS is also image-finite.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.LTS in
universe u v in
variable {State : Type u} {Label : Type v} (lts : LTS State Label) in
/-- Every finite-state LTS is also image-finite. -/
@[grind .]
instance Cslib.LTS.finiteState_imageFinite [Finite State] : lts.ImageFinite := inferInstance
