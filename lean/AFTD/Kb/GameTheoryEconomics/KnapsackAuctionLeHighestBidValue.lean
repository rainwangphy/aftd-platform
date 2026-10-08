import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionHighestBidValue

/-!
# KnapsackAuction.le_highestBidValue

Topic: mechanism_design   Node: bf2a45ec77a5

Provenance: formalization of a published result. Source: EconCSLib, `KnapsackAuction.le_highestBidValue`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Knapsack.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

KnapsackAuction.le_highestBidValue
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators in
variable {I : Type*} [Fintype I] [DecidableEq I] [LinearOrder I] [Nonempty I] in
omit [DecidableEq I] [LinearOrder I] in
lemma KnapsackAuction.le_highestBidValue (b : I → Nat) (i : I) :
    b i ≤ highestBidValue b := by
  classical
  exact Finset.le_sup' (s := Finset.univ) (f := b) (by simp)
