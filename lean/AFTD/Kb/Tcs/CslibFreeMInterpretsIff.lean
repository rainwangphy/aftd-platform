import AFTD.Prelude
import AFTD.Kb.Tcs.CslibFreeM
import AFTD.Kb.Tcs.CslibFreeMInterprets
import AFTD.Kb.Tcs.CslibFreeMLiftM
import AFTD.Kb.Tcs.CslibFreeMInterpretsEq
import AFTD.Kb.Tcs.CslibFreeMInterpretsLiftM
import AFTD.Kb.Tcs.CslibFreeMPureEqPure
import AFTD.Kb.Tcs.CslibFreeMBindEqBind
import AFTD.Kb.Tcs.CslibFreeMMapEqMap
import AFTD.Kb.Tcs.CslibFreeMLiftBindEq
import AFTD.Kb.Tcs.CslibFreeMPureBind
import AFTD.Kb.Tcs.CslibFreeMBindPure
import AFTD.Kb.Tcs.CslibFreeMBindPureComp
import AFTD.Kb.Tcs.CslibFreeMMapPure
import AFTD.Kb.Tcs.CslibFreeMMapBind
import AFTD.Kb.Tcs.CslibFreeMIdMap
import AFTD.Kb.Tcs.CslibFreeMLiftMPure
import AFTD.Kb.Tcs.CslibFreeMLiftMLiftBind
import AFTD.Kb.Tcs.CslibFreeMLiftMLift
import AFTD.Kb.Tcs.CslibFreeMLiftMBind
import AFTD.Kb.Tcs.CslibFreeMLiftMMap
import AFTD.Kb.Tcs.CslibFreeMLiftMSeq
import AFTD.Kb.Tcs.CslibFreeMLiftMSeqLeft
import AFTD.Kb.Tcs.CslibFreeMLiftMSeqRight
import AFTD.Kb.Tcs.CslibFreeMInstPure
import AFTD.Kb.Tcs.CslibFreeMInstBind
import AFTD.Kb.Tcs.CslibFreeMInstFunctor
import AFTD.Kb.Tcs.CslibFreeMInstLawfulFunctor
import AFTD.Kb.Tcs.CslibFreeMInstMonad
import AFTD.Kb.Tcs.CslibFreeMInstLawfulMonad
import AFTD.Kb.Tcs.F
import AFTD.Kb.Tcs.PFunctorFreeMLiftM
import AFTD.Kb.Tcs.PFunctorFreeMInterprets
import AFTD.Kb.Tcs.PFunctorFreeMInterpretsEq
import AFTD.Kb.Tcs.PFunctorFreeMInterpretsLiftM
import AFTD.Kb.Tcs.PFunctorFreeMInterpretsIff

/-!
# Cslib.FreeM.Interprets.iff

Topic: computability   Node: edd57fcb9a45

Provenance: formalization of a published result. Source: CSLib, `Cslib.FreeM.Interprets.iff`. Lean proof by Tanner Duve, Eric Wieser, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Control/Monad/Free.lean (Copyright (c) 2025 Tanner Duve. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The universal property of the free monad `FreeM`. That is, `liftM handler` is the unique interpreter that extends the effect handler `handler` to interpret `FreeM F` computations in a monad `m`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v w w' w'' in
variable {F : Type u → Type v} {ι : Type u} {α : Type w} {β : Type w'} {γ : Type w''} in
variable {m : Type u → Type w} [Monad m] {α β : Type u} in
/-- The universal property of the free monad `FreeM`. That is, `liftM handler` is the unique interpreter that extends the effect handler `handler` to interpret `FreeM F` computations in a monad `m`. -/
theorem Cslib.FreeM.Interprets.iff (handler : {ι : Type u} → F ι → m ι) (interp : FreeM F α → m α) :
    Interprets handler interp ↔ interp = (·.liftM handler) :=
  ⟨(·.eq), fun h => h ▸ Interprets.liftM _⟩
