import AFTD.Prelude
import AFTD.Kb.Tcs.CslibFreeM
import AFTD.Kb.Tcs.CslibFreeMBind
import AFTD.Kb.Tcs.CslibFreeMBindEqBind
import AFTD.Kb.Tcs.CslibFreeMInstPure
import AFTD.Kb.Tcs.CslibFreeMInstBind
import AFTD.Kb.Tcs.F

/-!
# Cslib.FreeM.map

Topic: computability   Node: 3344edb1f3d6

Provenance: formalization of a published result. Source: CSLib, `Cslib.FreeM.map`. Lean proof by Tanner Duve, Eric Wieser, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Control/Monad/Free.lean (Copyright (c) 2025 Tanner Duve. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Map a function over a `FreeM` monad. The builtin `<$>` notation should be preferred when `α` and `β` are in the same universe.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v w w' w'' in
variable {F : Type u → Type v} {ι : Type u} {α : Type w} {β : Type w'} {γ : Type w''} in
/-- Map a function over a `FreeM` monad. The builtin `<$>` notation should be preferred when `α` and `β` are in the same universe. -/
def Cslib.FreeM.map (f : α → β) : FreeM F α → FreeM F β
  | .pure a => .pure (f a)
  | .liftBind op cont => .liftBind op fun z => FreeM.map f (cont z)
