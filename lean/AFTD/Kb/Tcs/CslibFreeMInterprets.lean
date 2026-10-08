import AFTD.Prelude
import AFTD.Kb.Tcs.CslibFreeM
import AFTD.Kb.Tcs.CslibFreeMInstBind
import AFTD.Kb.Tcs.CslibFreeMLift
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
import AFTD.Kb.Tcs.CslibFreeMInstFunctor
import AFTD.Kb.Tcs.CslibFreeMInstLawfulFunctor
import AFTD.Kb.Tcs.CslibFreeMInstMonad
import AFTD.Kb.Tcs.CslibFreeMInstLawfulMonad
import AFTD.Kb.Tcs.F
import AFTD.Kb.Tcs.PFunctorFreeMInterprets

/-!
# Cslib.FreeM.Interprets

Topic: computability   Node: a9ed52a5e09a

Provenance: formalization of a published result. Source: CSLib, `Cslib.FreeM.Interprets`. Lean proof by Tanner Duve, Eric Wieser, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Control/Monad/Free.lean (Copyright (c) 2025 Tanner Duve. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A predicate stating that `interp : FreeM F α → m α` is an interpreter for the effect handler `handler : ∀ {α}, F α → m α`. This means that `interp` is a monad morphism from the free monad `FreeM F` to the monad `m`, and that it extends the interpretation of individual operations given by `f`. Formally, `interp` satisfies the two equations: - `interp (pure a) = pure a` - `interp (liftBind op k) = handler op >>= fun x => interp (k x)`
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v w w' w'' in
variable {F : Type u → Type v} {ι : Type u} {α : Type w} {β : Type w'} {γ : Type w''} in
variable {m : Type u → Type w} [Monad m] {α β : Type u} in
/-- A predicate stating that `interp : FreeM F α → m α` is an interpreter for the effect handler `handler : ∀ {α}, F α → m α`. This means that `interp` is a monad morphism from the free monad `FreeM F` to the monad `m`, and that it extends the interpretation of individual operations given by `f`. Formally, `interp` satisfies the two equations: - `interp (pure a) = pure a` - `interp (liftBind op k) = handler op >>= fun x => interp (k x)` -/
structure Cslib.FreeM.Interprets (handler : {ι : Type u} → F ι → m ι) (interp : FreeM F α → m α) : Prop where
  apply_pure (a : α) : interp (.pure a) = pure a
  apply_lift_bind {ι : Type u} (op : F ι) (cont : ι → FreeM F α) :
    interp (lift op >>= cont) = handler op >>= fun x => interp (cont x)
