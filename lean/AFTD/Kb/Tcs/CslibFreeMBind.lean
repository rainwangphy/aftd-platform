import AFTD.Prelude
import AFTD.Kb.Tcs.CslibFreeM
import AFTD.Kb.Tcs.CslibFreeMInstPure
import AFTD.Kb.Tcs.F

/-!
# Cslib.FreeM.bind

Topic: computability   Node: b14ba1e95607

Provenance: formalization of a published result. Source: CSLib, `Cslib.FreeM.bind`. Lean proof by Tanner Duve, Eric Wieser, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Control/Monad/Free.lean (Copyright (c) 2025 Tanner Duve. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Bind operation for the `FreeM` monad. The builtin `>>=` notation should be preferred when `α` and `β` are in the same universe.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v w w' w'' in
variable {F : Type u → Type v} {ι : Type u} {α : Type w} {β : Type w'} {γ : Type w''} in
/-- Bind operation for the `FreeM` monad. The builtin `>>=` notation should be preferred when `α` and `β` are in the same universe. -/
protected def Cslib.FreeM.bind (x : FreeM F α) (f : α → FreeM F β) : FreeM F β :=
  match x with
  | .pure a => f a
  | .liftBind op cont => .liftBind op fun z => FreeM.bind (cont z) f
