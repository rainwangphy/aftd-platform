import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionNatBinarySocialWelfare
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionDynamicProgrammingOptimalAllocation
import AFTD.Kb.GameTheoryEconomics.KnapsackAuction
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionCapacity

/-!
# KnapsackAuction.dynamicProgrammingOptimalValue

Topic: mechanism_design   Node: 2156d8c66d3f

Provenance: formalization of a published result. Source: EconCSLib, `KnapsackAuction.dynamicProgrammingOptimalValue`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Knapsack.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The social welfare achieved by the dynamic-programming allocation.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open KnapsackAuction in
open scoped BigOperators in
variable {I : Type*} [Fintype I] [DecidableEq I] in
/-- The social welfare achieved by the dynamic-programming allocation. -/
noncomputable def KnapsackAuction.dynamicProgrammingOptimalValue
    (w b : I → Nat) (capacity : Nat) : Nat :=
  natBinarySocialWelfare b (dynamicProgrammingOptimalAllocation w b capacity)
