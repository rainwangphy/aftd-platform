import AFTD.Prelude
import AFTD.Kb.Tcs.CslibFreeMInstMonad
import AFTD.Kb.Tcs.CslibFreeMInstFunctor
import AFTD.Kb.Tcs.CslibFreeMInstLawfulFunctor
import AFTD.Kb.Tcs.CslibFreeMInstBind
import AFTD.Kb.Tcs.CslibFreeMContF
import AFTD.Kb.Tcs.CslibFreeMInstFunctorContF
import AFTD.Kb.Tcs.CslibFreeMInstLawfulMonad
import AFTD.Kb.Tcs.CslibFreeMInstPure
import AFTD.Kb.Tcs.CslibFreeMFreeCont
import AFTD.Kb.Tcs.CslibFreeM

/-!
# Cslib.FreeM.FreeCont.run

Topic: computability   Node: 804fd2b80779

Provenance: formalization of a published result. Source: CSLib, `Cslib.FreeM.FreeCont.run`. Lean proof by Tanner Duve, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Control/Monad/Free/Effects.lean (Copyright (c) 2025 Tanner Duve. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Run a continuation computation with the given continuation.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v w w' w'' in
variable {r : Type u} {α : Type v} {β : Type w} in
/-- Run a continuation computation with the given continuation. -/
def Cslib.FreeM.FreeCont.run : FreeCont r α → (α → r) → r
  | .pure a, k => k a
  | .liftBind (.callCC g) cont, k => g (fun a => run (cont a) k)
