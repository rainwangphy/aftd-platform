import AFTD.Prelude
import AFTD.Kb.Tcs.PFunctorFreeM
import AFTD.Kb.Tcs.PFunctorFreeMInstMonad
import AFTD.Kb.Tcs.PFunctorFreeMIdMap
import AFTD.Kb.Tcs.PFunctorFreeMPureBind
import AFTD.Kb.Tcs.PFunctorFreeMBindAssoc
import AFTD.Kb.Tcs.PFunctorFreeMBindPureComp
import AFTD.Kb.Tcs.CslibFreeMBindAssoc
import AFTD.Kb.Tcs.CslibFreeMInstLawfulMonad

/-!
# PFunctor.FreeM.instLawfulMonad

Topic: algorithms   Node: 03b61b9e3a2f

Provenance: formalization of a published result. Source: CSLib, `PFunctor.FreeM.instLawfulMonad`. Lean proof by Quang Dao, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/PFunctor/Free.lean (Copyright (c) 2026 Quang Dao. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

PFunctor.FreeM.instLawfulMonad
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v uA uB in
variable {P : PFunctor.{uA, uB}} {α β γ : Type*} in
instance PFunctor.FreeM.instLawfulMonad : LawfulMonad (P.FreeM) := LawfulMonad.mk'
  (bind_pure_comp := bind_pure_comp)
  (id_map := id_map)
  (pure_bind := pure_bind)
  (bind_assoc := FreeM.bind_assoc)
