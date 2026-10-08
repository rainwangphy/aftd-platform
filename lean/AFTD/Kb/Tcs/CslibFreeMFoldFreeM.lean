import AFTD.Prelude
import AFTD.Kb.Tcs.CslibFreeMInstMonad
import AFTD.Kb.Tcs.CslibFreeMInstFunctor
import AFTD.Kb.Tcs.CslibFreeMInstLawfulFunctor
import AFTD.Kb.Tcs.CslibFreeMInstBind
import AFTD.Kb.Tcs.CslibFreeMInstLawfulMonad
import AFTD.Kb.Tcs.CslibFreeMInstPure
import AFTD.Kb.Tcs.CslibFreeM

/-!
# Cslib.FreeM.foldFreeM

Topic: computability   Node: a1f3ccf81598

Provenance: formalization of a published result. Source: CSLib, `Cslib.FreeM.foldFreeM`. Lean proof by Tanner Duve, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Control/Monad/Free/Fold.lean (Copyright (c) 2025 Tanner Duve. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Fold function for the `FreeM` monad
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v w w' in
variable {F : Type u → Type v} {ι : Type u} {α : Type w} {β : Type w'} in
/-- Fold function for the `FreeM` monad -/
def Cslib.FreeM.foldFreeM
    (onValue : α → β)
    (onEffect : {ι : Type u} → F ι → (ι → β) → β) :
    FreeM F α → β
  | .pure a => onValue a
  | .liftBind op k => onEffect op (fun x => foldFreeM onValue onEffect (k x))
