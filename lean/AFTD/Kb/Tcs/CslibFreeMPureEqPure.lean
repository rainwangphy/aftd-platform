import AFTD.Prelude
import AFTD.Kb.Tcs.CslibFreeMInstPure
import AFTD.Kb.Tcs.CslibFreeM

/-!
# Cslib.FreeM.pure_eq_pure

Topic: computability   Node: b53c6354b5fc

Provenance: formalization of a published result. Source: CSLib, `Cslib.FreeM.pure_eq_pure`. Lean proof by Tanner Duve, Eric Wieser, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Control/Monad/Free.lean (Copyright (c) 2025 Tanner Duve. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.FreeM.pure_eq_pure
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v w w' w'' in
variable {F : Type u → Type v} {ι : Type u} {α : Type w} {β : Type w'} {γ : Type w''} in
@[simp]
theorem Cslib.FreeM.pure_eq_pure : FreeM.pure = (pure : α → FreeM F α) := rfl
