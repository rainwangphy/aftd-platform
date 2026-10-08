import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMState
import AFTD.Kb.Tcs.CslibURMStateInit
import AFTD.Kb.Tcs.CslibURMStateInstDecidableIsHalted

/-!
# Cslib.URM.State.instInhabited

Topic: computability   Node: 79c2b46cbaa1

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.State.instInhabited`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/Defs.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.URM.State.instInhabited
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
instance Cslib.URM.State.instInhabited : Inhabited State := ⟨init []⟩
