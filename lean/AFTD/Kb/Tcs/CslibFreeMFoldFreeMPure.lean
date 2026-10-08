import AFTD.Prelude
import AFTD.Kb.Tcs.CslibFreeMInstMonad
import AFTD.Kb.Tcs.CslibFreeMInstFunctor
import AFTD.Kb.Tcs.CslibFreeMInstLawfulFunctor
import AFTD.Kb.Tcs.CslibFreeMInstBind
import AFTD.Kb.Tcs.CslibFreeMFoldFreeM
import AFTD.Kb.Tcs.CslibFreeMInstLawfulMonad
import AFTD.Kb.Tcs.CslibFreeMInstPure
import AFTD.Kb.Tcs.CslibFreeM

/-!
# Cslib.FreeM.foldFreeM_pure

Topic: computability   Node: 08217f5d63b0

Provenance: formalization of a published result. Source: CSLib, `Cslib.FreeM.foldFreeM_pure`. Lean proof by Tanner Duve, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Control/Monad/Free/Fold.lean (Copyright (c) 2025 Tanner Duve. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.FreeM.foldFreeM_pure
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v w w' in
variable {F : Type u → Type v} {ι : Type u} {α : Type w} {β : Type w'} in
@[simp]
theorem Cslib.FreeM.foldFreeM_pure
    (onValue : α → β)
    (onEffect : {ι : Type u} → F ι → (ι → β) → β)
    (a : α) : foldFreeM onValue onEffect (pure a) = onValue a := rfl
