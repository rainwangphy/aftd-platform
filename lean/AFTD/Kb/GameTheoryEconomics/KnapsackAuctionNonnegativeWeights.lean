import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.KnapsackAuction
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# KnapsackAuction.NonnegativeWeights

Topic: mechanism_design   Node: 8d40efbd7513

Provenance: formalization of a published result. Source: EconCSLib, `KnapsackAuction.NonnegativeWeights`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Knapsack.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Every public weight is nonnegative.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators in
variable {I : Type*} {U : Type*} [Field U] [LinearOrder U] [IsStrictOrderedRing U] in
/-- Every public weight is nonnegative. -/
def KnapsackAuction.NonnegativeWeights (A : KnapsackAuction I U) : Prop :=
  ∀ i, 0 ≤ A.weight i
