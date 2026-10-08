import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionBinaryAllocation
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionDpSolveList
import AFTD.Kb.GameTheoryEconomics.KnapsackAuction
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionCapacity

/-!
# KnapsackAuction.dynamicProgrammingOptimalAllocation

Topic: mechanism_design   Node: 4956ca46fc73

Provenance: formalization of a published result. Source: EconCSLib, `KnapsackAuction.dynamicProgrammingOptimalAllocation`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Knapsack.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The computable knapsack allocation obtained by running the dynamic program on the full finite agent list.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open KnapsackAuction in
open scoped BigOperators in
variable {I : Type*} [Fintype I] [DecidableEq I] in
/-- The computable knapsack allocation obtained by running the dynamic program on the full finite agent list. -/
noncomputable def KnapsackAuction.dynamicProgrammingOptimalAllocation
    (w b : I → Nat) (capacity : Nat) : BinaryAllocation I :=
  dpSolveList w b ((Finset.univ : Finset I).toList) capacity
