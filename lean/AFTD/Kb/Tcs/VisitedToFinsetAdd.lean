import AFTD.Prelude
import AFTD.Kb.Tcs.Visited
import AFTD.Kb.Tcs.VisitedToFinset
import AFTD.Kb.Tcs.VisitedInstAdd
import AFTD.Kb.Tcs.VisitedToFinsetZero
import AFTD.Kb.Tcs.VisitedInstZero

/-!
# Visited.toFinset_add

Topic: algorithms   Node: dc8742387454

Provenance: formalization of a published result. Source: EconCSLib, `Visited.toFinset_add`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/CostM/Visited.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Visited.toFinset_add
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {A : Type*} in
variable [DecidableEq A] in
@[simp] theorem Visited.toFinset_add (a b : Visited A) :
    (a + b).toFinset = a.toFinset ∪ b.toFinset := rfl
