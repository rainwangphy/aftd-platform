import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AuctionReserveSecondPriceUtility
import AFTD.Kb.GameTheoryEconomics.AuctionReserveSecondPriceAllocation
import AFTD.Kb.GameTheoryEconomics.AuctionReserveSecondPriceClearingPrice
import AFTD.Kb.GameTheoryEconomics.AuctionReserveSecondPriceUtilityWinner
import AFTD.Kb.GameTheoryEconomics.AuctionMaxBidExcluding
import AFTD.Kb.GameTheoryEconomics.AuctionReserveSecondPriceClearingPriceEqMaxReserveExcludingOfAllocationEqSome
import AFTD.Kb.GameTheoryEconomics.AuctionMaxBidExcludingUpdateSelf
import AFTD.Kb.GameTheoryEconomics.AuctionReserveSecondPriceUtilityLoser
import AFTD.Kb.GameTheoryEconomics.AuctionReserveSecondPriceBidLeClearingThresholdOfNotAllocationUpdateSelf
import AFTD.Kb.GameTheoryEconomics.AuctionReserveSecondPriceUtilityNonneg

/-!
# Auction.ReserveSecondPrice.valuation_is_dominant

Topic: mechanism_design   Node: 7390b5ec5b50

Provenance: formalization of a published result. Source: EconCSLib, `Auction.ReserveSecondPrice.valuation_is_dominant`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/ReserveVickrey.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Truthful bidding dominates any other bid in the reserve second-price auction.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} [Fintype I] [Nontrivial I] [DecidableEq I] in
variable {U : Type*} [AddCommGroup U] [LinearOrder U] [IsOrderedAddMonoid U] in
variable {reserve : U} {v : I → U} in
/-- Truthful bidding dominates any other bid in the reserve second-price auction. -/
theorem Auction.ReserveSecondPrice.valuation_is_dominant (reserve : U) (v : I → U) (i : I) (b : I → U) :
    utility reserve v b i ≤ utility reserve v (Function.update b i (v i)) i := by
  let bTruth := Function.update b i (v i)
  by_cases hcurrent : allocation reserve b = some i
  · rw [utility_winner hcurrent]
    by_cases htruth : allocation reserve bTruth = some i
    · rw [utility_winner htruth]
      have hcurrent_price :
          clearingPrice reserve b = max reserve (Auction.maxBidExcluding b i) :=
        clearingPrice_eq_max_reserve_excluding_of_allocation_eq_some hcurrent
      have htruth_price :
          clearingPrice reserve bTruth = max reserve (Auction.maxBidExcluding b i) := by
        calc
          clearingPrice reserve bTruth
              = max reserve (Auction.maxBidExcluding bTruth i) :=
                clearingPrice_eq_max_reserve_excluding_of_allocation_eq_some htruth
          _ = max reserve (Auction.maxBidExcluding b i) := by
                simp [bTruth, Auction.maxBidExcluding_update_self]
      rw [hcurrent_price, htruth_price]
    · rw [utility_loser htruth]
      have hthreshold :
          v i ≤ clearingPrice reserve b := by
        have hprice :
            clearingPrice reserve b = max reserve (Auction.maxBidExcluding b i) :=
          clearingPrice_eq_max_reserve_excluding_of_allocation_eq_some hcurrent
        have hle :
            v i ≤ max reserve (Auction.maxBidExcluding b i) := by
          simpa [bTruth] using
            bid_le_clearing_threshold_of_not_allocation_update_self reserve b i (v i) htruth
        simpa [hprice] using hle
      exact sub_nonpos.mpr hthreshold
  · rw [utility_loser hcurrent]
    exact utility_nonneg (reserve := reserve) (v := v)
      (b := Function.update b i (v i)) (i := i) (by simp)
