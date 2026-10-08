import AFTD.Prelude
import AFTD.Kb.Tcs.CslibFreeM
import AFTD.Kb.Tcs.CslibFreeMBind
import AFTD.Kb.Tcs.CslibFreeMInstBind
import AFTD.Kb.Tcs.CslibFreeMInstPure
import AFTD.Kb.Tcs.F

/-!
# Cslib.FreeM.bind_eq_bind

Topic: computability   Node: 3b24877d73a8

Provenance: formalization of a published result. Source: CSLib, `Cslib.FreeM.bind_eq_bind`. Lean proof by Tanner Duve, Eric Wieser, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Control/Monad/Free.lean (Copyright (c) 2025 Tanner Duve. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Note that this lemma does not always apply, as it is universe-constrained by `Bind.bind`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v w w' w'' in
variable {F : Type u → Type v} {ι : Type u} {α : Type w} {β : Type w'} {γ : Type w''} in
/-- Note that this lemma does not always apply, as it is universe-constrained by `Bind.bind`. -/
@[simp]
theorem Cslib.FreeM.bind_eq_bind {α β : Type w} : (FreeM.bind : FreeM F α → _ → FreeM F β) = Bind.bind := rfl
