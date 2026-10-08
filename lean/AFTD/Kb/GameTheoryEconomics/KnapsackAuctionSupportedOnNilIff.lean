import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionBinaryAllocation
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionSupportedOn
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionEqFalseOfSupportedOnOfNotMem

/-!
# KnapsackAuction.supportedOn_nil_iff

Topic: mechanism_design   Node: e92969d5152d

Provenance: formalization of a published result. Source: EconCSLib, `KnapsackAuction.supportedOn_nil_iff`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Knapsack.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

KnapsackAuction.supportedOn_nil_iff
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators in
variable {I : Type*} [Fintype I] [DecidableEq I] in
omit [Fintype I] [DecidableEq I] in
lemma KnapsackAuction.supportedOn_nil_iff {x : BinaryAllocation I} :
    supportedOn ([] : List I) x ↔ x = fun _ => false := by
  constructor
  · intro hsupp
    funext i
    exact eq_false_of_supportedOn_of_not_mem hsupp (by simp)
  · intro hx i hi
    simp [hx] at hi
