import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionBinaryAllocation

/-!
# KnapsackAuction.natBinarySocialWelfare

Topic: mechanism_design   Node: 9bc30d796041

Provenance: formalization of a published result. Source: EconCSLib, `KnapsackAuction.natBinarySocialWelfare`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Knapsack.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Integer-valued welfare of a binary allocation profile.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators in
variable {I : Type*} [Fintype I] [DecidableEq I] in
/-- Integer-valued welfare of a binary allocation profile. -/
def KnapsackAuction.natBinarySocialWelfare (b : I → Nat) (x : BinaryAllocation I) : Nat :=
  ∑ i, if x i then b i else 0
