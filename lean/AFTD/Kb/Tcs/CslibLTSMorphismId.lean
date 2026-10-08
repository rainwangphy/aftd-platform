import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTSCat
import AFTD.Kb.Tcs.CslibLTSMorphism
import AFTD.Kb.Tcs.CslibLTS

/-!
# Cslib.LTS.Morphism.id

Topic: computability   Node: 02112c814c04

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.Morphism.id`. Lean proof by Ayberk Tosun, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/LTSCat/Basic.lean (Copyright (c) 2026 Ayberk Tosun (Zeroth Research). All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The identity LTS morphism.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {State Label : Type*} in
/-- The identity LTS morphism. -/
def Cslib.LTS.Morphism.id (lts : LTSCat) : LTS.Morphism lts lts where
  stateMap := _root_.id
  labelMap := pure
  labelMap_tr _ _ _ := _root_.id
