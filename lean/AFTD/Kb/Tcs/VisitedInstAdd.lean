import AFTD.Prelude
import AFTD.Kb.Tcs.Visited
import AFTD.Kb.Tcs.VisitedOfFinset
import AFTD.Kb.Tcs.VisitedToFinset
import AFTD.Kb.Tcs.VisitedToFinsetOfFinset
import AFTD.Kb.Tcs.VisitedToFinsetZero
import AFTD.Kb.Tcs.VisitedInstZero

/-!
# Visited.instAdd

Topic: algorithms   Node: 2a5bc4d18f96

Provenance: formalization of a published result. Source: EconCSLib, `Visited.instAdd`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/CostM/Visited.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Visited.instAdd
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {A : Type*} in
variable [DecidableEq A] in
instance Visited.instAdd : Add (Visited A) :=
  ⟨fun a b => (ofFinset (a.toFinset ∪ b.toFinset))⟩
