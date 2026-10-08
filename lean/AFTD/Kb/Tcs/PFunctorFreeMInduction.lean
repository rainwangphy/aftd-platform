import AFTD.Prelude
import AFTD.Kb.Tcs.PFunctorFreeM
import AFTD.Kb.Tcs.PFunctorFreeMInstPure
import AFTD.Kb.Tcs.PFunctorFreeMBind
import AFTD.Kb.Tcs.PFunctorFreeMLift
import AFTD.Kb.Tcs.PFunctorFreeMLiftNePure
import AFTD.Kb.Tcs.PFunctorFreeMPureNeLift
import AFTD.Kb.Tcs.PFunctorFreeMBindEqBind
import AFTD.Kb.Tcs.PFunctorFreeMLiftBindEq
import AFTD.Kb.Tcs.CslibFreeMBind
import AFTD.Kb.Tcs.CslibFreeMLift
import AFTD.Kb.Tcs.CslibFreeMInduction

/-!
# PFunctor.FreeM.induction

Topic: algorithms   Node: e3221b5e931b

Provenance: formalization of a published result. Source: CSLib, `PFunctor.FreeM.induction`. Lean proof by Quang Dao, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/PFunctor/Free.lean (Copyright (c) 2026 Quang Dao. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An override for the default induction principle that is in simp-normal form. Note that when `α` and `P.B a` are in the same universe, this simplifies slightly further.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v uA uB in
variable {P : PFunctor.{uA, uB}} {α β γ : Type*} in
set_option linter.unusedVariables false in
/-- An override for the default induction principle that is in simp-normal form. Note that when `α` and `P.B a` are in the same universe, this simplifies slightly further. -/
@[induction_eliminator]
protected theorem PFunctor.FreeM.induction {motive : P.FreeM α → Prop}
    (pure : ∀ a, motive (pure a))
    (lift_bind : ∀ (a : P.A) (cont : P.B a → P.FreeM α) (ih : ∀ i, motive (cont i)),
      motive ((FreeM.lift a).bind cont)) : ∀ x, motive x
  | .pure a => pure a
  | liftBind a cont => lift_bind a cont fun u => FreeM.induction pure lift_bind (cont u)
