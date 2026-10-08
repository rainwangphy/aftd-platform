import AFTD.Prelude
import AFTD.Kb.Tcs.PFunctorFreeM
import AFTD.Kb.Tcs.PFunctorFreeMInterprets
import AFTD.Kb.Tcs.PFunctorFreeMLiftM
import AFTD.Kb.Tcs.PFunctorFreeMInterpretsEq
import AFTD.Kb.Tcs.PFunctorFreeMInterpretsLiftM
import AFTD.Kb.Tcs.PFunctorFreeMLiftMLiftBind
import AFTD.Kb.Tcs.CslibFreeMLiftM

/-!
# PFunctor.FreeM.Interprets.iff

Topic: algorithms   Node: effaf9bc7a26

Provenance: formalization of a published result. Source: CSLib, `PFunctor.FreeM.Interprets.iff`. Lean proof by Quang Dao, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/PFunctor/Free.lean (Copyright (c) 2026 Quang Dao. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The universal property of the free monad `P.FreeM`. That is, `liftM handler` is the unique interpreter that extends the effect handler `handler` to interpret `P.FreeM` computations in a monad `m`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v uA uB in
variable {P : PFunctor.{uA, uB}} {α β γ : Type*} in
variable {m : Type uB → Type v} {α : Type uB} in
variable [Monad m] (interp : (a : P.A) → m (P.B a)) in
/-- The universal property of the free monad `P.FreeM`. That is, `liftM handler` is the unique interpreter that extends the effect handler `handler` to interpret `P.FreeM` computations in a monad `m`. -/
theorem PFunctor.FreeM.Interprets.iff (handler : (a : P.A) → m (P.B a)) (eval : P.FreeM α → m α) :
    Interprets handler eval ↔ eval = (·.liftM handler) :=
  ⟨(·.eq), fun h => h ▸ Interprets.liftM _⟩
