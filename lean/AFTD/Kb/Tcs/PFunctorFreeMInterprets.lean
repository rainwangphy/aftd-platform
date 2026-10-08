import AFTD.Prelude
import AFTD.Kb.Tcs.PFunctorFreeM
import AFTD.Kb.Tcs.PFunctorFreeMBind
import AFTD.Kb.Tcs.PFunctorFreeMLift
import AFTD.Kb.Tcs.PFunctorFreeMLiftNePure
import AFTD.Kb.Tcs.PFunctorFreeMPureNeLift
import AFTD.Kb.Tcs.PFunctorFreeMBindEqBind
import AFTD.Kb.Tcs.PFunctorFreeMLiftBindEq
import AFTD.Kb.Tcs.PFunctorFreeMBindPure
import AFTD.Kb.Tcs.PFunctorFreeMBindPureComp
import AFTD.Kb.Tcs.PFunctorFreeMLiftBindBind
import AFTD.Kb.Tcs.PFunctorFreeMLiftMLiftBind
import AFTD.Kb.Tcs.CslibFreeMBind
import AFTD.Kb.Tcs.CslibFreeMLift

/-!
# PFunctor.FreeM.Interprets

Topic: algorithms   Node: b23df41613a4

Provenance: formalization of a published result. Source: CSLib, `PFunctor.FreeM.Interprets`. Lean proof by Quang Dao, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/PFunctor/Free.lean (Copyright (c) 2026 Quang Dao. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A predicate stating that `eval : P.FreeM α → m α` is an interpreter for the polynomial effect handler `handler : (a : P.A) → m (P.B a)`. This means that `eval` is a monad morphism from the free monad `P.FreeM` to the monad `m`, and that it extends the interpretation of individual operations given by `handler`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v uA uB in
variable {P : PFunctor.{uA, uB}} {α β γ : Type*} in
variable {m : Type uB → Type v} {α : Type uB} in
variable [Monad m] (interp : (a : P.A) → m (P.B a)) in
/-- A predicate stating that `eval : P.FreeM α → m α` is an interpreter for the polynomial effect handler `handler : (a : P.A) → m (P.B a)`. This means that `eval` is a monad morphism from the free monad `P.FreeM` to the monad `m`, and that it extends the interpretation of individual operations given by `handler`. -/
structure PFunctor.FreeM.Interprets (handler : (a : P.A) → m (P.B a)) (eval : P.FreeM α → m α) : Prop where
  apply_pure (a : α) : eval (.pure a) = pure a
  apply_lift_bind (a : P.A) (cont : P.B a → P.FreeM α) :
    eval ((FreeM.lift a).bind cont) = handler a >>= fun x => eval (cont x)
