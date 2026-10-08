import AFTD.Prelude
import AFTD.Kb.Tcs.Visited
import AFTD.Kb.Tcs.VisitedToFinsetZero
import AFTD.Kb.Tcs.VisitedInstZero

/-!
# Visited.singleton

Topic: algorithms   Node: e7db8456eb49

Provenance: formalization of a published result. Source: EconCSLib, `Visited.singleton`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/CostM/Visited.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Mark a single sub-problem `a` as visited.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {A : Type*} in
/-- Mark a single sub-problem `a` as visited. -/
def Visited.singleton (a : A) : Visited A := ({a} : Finset A)
