import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMState
import AFTD.Kb.Tcs.CslibURMStateInstDecidableIsHalted
import AFTD.Kb.Tcs.CslibURMStateInstInhabited

/-!
# Cslib.URM.State.instRepr

Topic: computability   Node: b17c234bd4a3

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.State.instRepr`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/Defs.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.URM.State.instRepr
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
instance Cslib.URM.State.instRepr : Repr State where
  reprPrec s _ := s!"State(pc={s.pc})"
