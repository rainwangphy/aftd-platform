import AFTD.Prelude
import AFTD.Kb.Tcs.CslibFreeMInstMonad
import AFTD.Kb.Tcs.CslibFreeMInstFunctor
import AFTD.Kb.Tcs.CslibFreeMInstLawfulFunctor
import AFTD.Kb.Tcs.CslibFreeMInstBind
import AFTD.Kb.Tcs.CslibFreeMInstLawfulMonad
import AFTD.Kb.Tcs.CslibFreeMInstPure
import AFTD.Kb.Tcs.CslibFreeM

/-!
# Cslib.FreeM.liftM

Topic: computability   Node: 63052865a093

Provenance: formalization of a published result. Source: CSLib, `Cslib.FreeM.liftM`. Lean proof by Tanner Duve, Eric Wieser, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Control/Monad/Free.lean (Copyright (c) 2025 Tanner Duve. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Interpret a `FreeM F` computation into any monad `m` by providing an interpretation function for the effect signature `F`. This function defines the *canonical interpreter* from the free monad `FreeM F` into the target monad `m`. It is the unique monad morphism that extends the effect handler `interp : ∀ {β}, F β → m β` via the universal property of `FreeM`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v w w' w'' in
variable {F : Type u → Type v} {ι : Type u} {α : Type w} {β : Type w'} {γ : Type w''} in
variable {m : Type u → Type w} [Monad m] {α β : Type u} in
/-- Interpret a `FreeM F` computation into any monad `m` by providing an interpretation function for the effect signature `F`. This function defines the *canonical interpreter* from the free monad `FreeM F` into the target monad `m`. It is the unique monad morphism that extends the effect handler `interp : ∀ {β}, F β → m β` via the universal property of `FreeM`. -/
protected def Cslib.FreeM.liftM (interp : {ι : Type u} → F ι → m ι) : FreeM F α → m α
  | .pure a => pure a
  | .liftBind op cont => interp op >>= fun result => (cont result).liftM interp
