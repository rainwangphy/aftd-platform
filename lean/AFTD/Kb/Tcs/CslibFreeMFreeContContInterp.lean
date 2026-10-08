import AFTD.Prelude
import AFTD.Kb.Tcs.CslibFreeMContF
import AFTD.Kb.Tcs.CslibFreeMInstFunctorContF
import AFTD.Kb.Tcs.G

/-!
# Cslib.FreeM.FreeCont.contInterp

Topic: computability   Node: c4dcc4c3d121

Provenance: formalization of a published result. Source: CSLib, `Cslib.FreeM.FreeCont.contInterp`. Lean proof by Tanner Duve, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Control/Monad/Free/Effects.lean (Copyright (c) 2025 Tanner Duve. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Interpret `ContF r` operations into `ContT r Id`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v w w' w'' in
variable {r : Type u} {α : Type v} {β : Type w} in
/-- Interpret `ContF r` operations into `ContT r Id`. -/
@[simp]
def Cslib.FreeM.FreeCont.contInterp : ContF r α → ContT r Id α | .callCC g => .mk fun k => pure <| g fun a => (k a).run
