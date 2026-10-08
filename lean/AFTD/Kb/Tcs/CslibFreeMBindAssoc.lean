import AFTD.Prelude
import AFTD.Kb.Tcs.CslibFreeM
import AFTD.Kb.Tcs.CslibFreeMBind
import AFTD.Kb.Tcs.CslibFreeMInduction
import AFTD.Kb.Tcs.CslibFreeMInstPure
import AFTD.Kb.Tcs.CslibFreeMLift
import AFTD.Kb.Tcs.CslibFreeMLiftBindEq
import AFTD.Kb.Tcs.CslibFreeMBindEqBind
import AFTD.Kb.Tcs.CslibFreeMInstBind
import AFTD.Kb.Tcs.CslibFreeMInstFunctor
import AFTD.Kb.Tcs.F
import AFTD.Kb.Tcs.G

/-!
# Cslib.FreeM.bind_assoc

Topic: computability   Node: aeb48bfe6dbe

Provenance: formalization of a published result. Source: CSLib, `Cslib.FreeM.bind_assoc`. Lean proof by Tanner Duve, Eric Wieser, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Control/Monad/Free.lean (Copyright (c) 2025 Tanner Duve. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.FreeM.bind_assoc
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v w w' w'' in
variable {F : Type u → Type v} {ι : Type u} {α : Type w} {β : Type w'} {γ : Type w''} in
protected theorem Cslib.FreeM.bind_assoc (x : FreeM F α) (f : α → FreeM F β) (g : β → FreeM F γ) :
    (x.bind f).bind g = x.bind (fun x => (f x).bind g) := by
  induction x with
  | pure a => rfl
  | lift_bind op cont ih => simp [← liftBind_eq, FreeM.bind, ih] at *
