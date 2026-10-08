import AFTD.Prelude
import AFTD.Kb.Tcs.Visited
import AFTD.Kb.Tcs.VisitedInstZero
import AFTD.Kb.Tcs.VisitedInstAdd
import AFTD.Kb.Tcs.VisitedExt
import AFTD.Kb.Tcs.VisitedToFinset
import AFTD.Kb.Tcs.VisitedToFinsetZero
import AFTD.Kb.Tcs.VisitedToFinsetAdd

/-!
# Visited.instAddMonoid

Topic: algorithms   Node: 3cd5a232278f

Provenance: formalization of a published result. Source: EconCSLib, `Visited.instAddMonoid`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/CostM/Visited.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Visited.instAddMonoid
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {A : Type*} in
variable [DecidableEq A] in
instance Visited.instAddMonoid : AddMonoid (Visited A) where
  add_assoc a b c := by ext; simp [Finset.union_assoc]
  zero_add a := by ext; simp
  add_zero a := by ext; simp
  nsmul := nsmulRec
