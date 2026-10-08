import AFTD.Prelude
import AFTD.Kb.Tcs.CslibFreeMFreeCont
import AFTD.Kb.Tcs.CslibFreeMLiftM
import AFTD.Kb.Tcs.CslibFreeMContF
import AFTD.Kb.Tcs.CslibFreeMFreeContContInterp
import AFTD.Kb.Tcs.CslibFreeMInstPure
import AFTD.Kb.Tcs.CslibFreeMInstBind
import AFTD.Kb.Tcs.CslibFreeMInstFunctor
import AFTD.Kb.Tcs.CslibFreeMInstLawfulFunctor
import AFTD.Kb.Tcs.CslibFreeMInstMonad
import AFTD.Kb.Tcs.CslibFreeMInstLawfulMonad
import AFTD.Kb.Tcs.CslibFreeMInstFunctorContF

/-!
# Cslib.FreeM.FreeCont.toContT

Topic: computability   Node: 979be2c7e2bc

Provenance: formalization of a published result. Source: CSLib, `Cslib.FreeM.FreeCont.toContT`. Lean proof by Tanner Duve, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Control/Monad/Free/Effects.lean (Copyright (c) 2025 Tanner Duve. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Convert a `FreeCont` computation into a `ContT` computation. This is the canonical interpreter derived from `liftM`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v w w' w'' in
variable {r : Type u} {α : Type v} {β : Type w} in
/-- Convert a `FreeCont` computation into a `ContT` computation. This is the canonical interpreter derived from `liftM`. -/
abbrev Cslib.FreeM.FreeCont.toContT {α : Type u} (comp : FreeCont r α) : ContT r Id α :=
  comp.liftM contInterp
