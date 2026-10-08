import AFTD.Prelude
import AFTD.Kb.Tcs.PFunctorFreeM
import AFTD.Kb.Tcs.PFunctorFreeMMap
import AFTD.Kb.Tcs.PFunctorFreeMLift
import AFTD.Kb.Tcs.PFunctorFreeMLiftNePure
import AFTD.Kb.Tcs.PFunctorFreeMPureNeLift
import AFTD.Kb.Tcs.PFunctorFreeMMapEqMap
import AFTD.Kb.Tcs.PFunctorFreeMLiftBindEq
import AFTD.Kb.Tcs.CslibFreeMMap

/-!
# PFunctor.FreeM.liftObj

Topic: algorithms   Node: 2bf9c4d46a4a

Provenance: formalization of a published result. Source: CSLib, `PFunctor.FreeM.liftObj`. Lean proof by Quang Dao, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/PFunctor/Free.lean (Copyright (c) 2026 Quang Dao. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Lift an object of the base polynomial functor into the free monad. This lifts the shape `x.1` with `lift` and relabels the responses with `x.2`. We use the universe-polymorphic `FreeM.map` rather than `<$>`, since the response type `P.B x.1` and the target `α` need not lie in the same universe.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v uA uB in
variable {P : PFunctor.{uA, uB}} {α β γ : Type*} in
/-- Lift an object of the base polynomial functor into the free monad. This lifts the shape `x.1` with `lift` and relabels the responses with `x.2`. We use the universe-polymorphic `FreeM.map` rather than `<$>`, since the response type `P.B x.1` and the target `α` need not lie in the same universe. -/
abbrev PFunctor.FreeM.liftObj (x : P.Obj α) : P.FreeM α := (lift x.1).map x.2
