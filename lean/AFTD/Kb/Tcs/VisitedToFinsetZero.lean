import AFTD.Prelude
import AFTD.Kb.Tcs.VisitedToFinset
import AFTD.Kb.Tcs.Visited
import AFTD.Kb.Tcs.VisitedInstZero

/-!
# Visited.toFinset_zero

Topic: algorithms   Node: eaf21ad99264

Provenance: formalization of a published result. Source: EconCSLib, `Visited.toFinset_zero`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/CostM/Visited.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Visited.toFinset_zero
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {A : Type*} in
@[simp] theorem Visited.toFinset_zero : (0 : Visited A).toFinset = ∅ := rfl
