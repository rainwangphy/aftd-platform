import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionBinaryAllocation
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionFractionalSocialWelfare
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionRealBidOfNat
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionBinaryToAllocation
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionNatBinarySocialWelfare

/-!
# KnapsackAuction.fractionalSocialWelfare_realBidOfNat_binaryToAllocation

Topic: mechanism_design   Node: 0ace1af8ab82

Provenance: formalization of a published result. Source: EconCSLib, `KnapsackAuction.fractionalSocialWelfare_realBidOfNat_binaryToAllocation`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Knapsack.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

KnapsackAuction.fractionalSocialWelfare_realBidOfNat_binaryToAllocation
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators in
variable {I : Type*} [Fintype I] [DecidableEq I] [LinearOrder I] [Nonempty I] in
omit [DecidableEq I] [LinearOrder I] [Nonempty I] in
lemma KnapsackAuction.fractionalSocialWelfare_realBidOfNat_binaryToAllocation
    (b : I → Nat) (x : BinaryAllocation I) :
    fractionalSocialWelfare (realBidOfNat b) (binaryToAllocation x) =
      natBinarySocialWelfare b x := by
  simp [fractionalSocialWelfare, realBidOfNat, binaryToAllocation, natBinarySocialWelfare]
