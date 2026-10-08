import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.KnapsackAuction

/-!
# KnapsackAuction.capacity

Topic: mechanism_design   Node: f2983b993a91

Provenance: formalization of a published result. Source: EconCSLib, `KnapsackAuction.capacity`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Knapsack.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The total capacity bound.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators in
variable {I : Type*} {U : Type*} [Field U] [LinearOrder U] [IsStrictOrderedRing U] in
/-- The total capacity bound. -/
abbrev KnapsackAuction.capacity (A : KnapsackAuction I U) : U :=
  A.totalCapacity
