import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionBinaryAllocation

/-!
# KnapsackAuction.supportedOn

Topic: mechanism_design   Node: 16154aa0c544

Provenance: formalization of a published result. Source: EconCSLib, `KnapsackAuction.supportedOn`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Knapsack.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An allocation is supported on a list of agents if every selected agent appears in that list.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators in
variable {I : Type*} [Fintype I] [DecidableEq I] in
/-- An allocation is supported on a list of agents if every selected agent appears in that list. -/
def KnapsackAuction.supportedOn (items : List I) (x : BinaryAllocation I) : Prop :=
  ∀ i, x i = true → i ∈ items
