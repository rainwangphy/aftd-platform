import AFTD.Prelude
import AFTD.Kb.Tcs.CslibFreeMInstFunctor
import AFTD.Kb.Tcs.CslibFreeMLiftBindEq
import AFTD.Kb.Tcs.CslibFreeMBindEqBind
import AFTD.Kb.Tcs.CslibFreeMInstBind
import AFTD.Kb.Tcs.CslibFreeMBind
import AFTD.Kb.Tcs.CslibFreeMInstPure
import AFTD.Kb.Tcs.CslibFreeMLift
import AFTD.Kb.Tcs.CslibFreeM

/-!
# Cslib.FreeM.induction

Topic: computability   Node: 6a8953030717

Provenance: formalization of a published result. Source: CSLib, `Cslib.FreeM.induction`. Lean proof by Tanner Duve, Eric Wieser, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Control/Monad/Free.lean (Copyright (c) 2025 Tanner Duve. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An override for the default induction principle that is in simp-normal form. Note that when `α` and `ι` are in the same universe, this simplifies slightly further.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v w w' w'' in
variable {F : Type u → Type v} {ι : Type u} {α : Type w} {β : Type w'} {γ : Type w''} in
set_option linter.unusedVariables false in
/-- An override for the default induction principle that is in simp-normal form. Note that when `α` and `ι` are in the same universe, this simplifies slightly further. -/
@[induction_eliminator]
protected theorem Cslib.FreeM.induction {motive : FreeM F α → Prop}
    (pure : ∀ a, motive (pure a))
    (lift_bind : ∀ {ι} (op : F ι) (cont : ι → FreeM F α) (ih : ∀ i, motive (cont i)),
      motive ((lift op).bind cont)) : ∀ x, motive x
  | .pure a => pure a
  | liftBind _ _ => lift_bind _ _ fun _ => FreeM.induction pure lift_bind _
