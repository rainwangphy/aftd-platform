import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AuctionReserveSecondPriceAllocation
import AFTD.Kb.GameTheoryEconomics.AuctionMaxBidExcluding
import AFTD.Kb.GameTheoryEconomics.AuctionSecondPriceWinner
import AFTD.Kb.GameTheoryEconomics.AuctionBidLeMaxBid
import AFTD.Kb.GameTheoryEconomics.AuctionMaxBid
import AFTD.Kb.GameTheoryEconomics.AuctionMaxBidExcludingEqMaxBidOfNotArgmax
import AFTD.Kb.GameTheoryEconomics.AuctionArgmaxBid
import AFTD.Kb.GameTheoryEconomics.AuctionArgmaxBidEqMaxBid
import AFTD.Kb.GameTheoryEconomics.AuctionMaxBidExcludingUpdateSelf

/-!
# Auction.ReserveSecondPrice.bid_le_clearing_threshold_of_not_allocation_update_self

Topic: mechanism_design   Node: d597f463c744

Provenance: formalization of a published result. Source: EconCSLib, `Auction.ReserveSecondPrice.bid_le_clearing_threshold_of_not_allocation_update_self`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/ReserveVickrey.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Auction.ReserveSecondPrice.bid_le_clearing_threshold_of_not_allocation_update_self
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} [Fintype I] [Nontrivial I] [DecidableEq I] in
variable {U : Type*} [AddCommGroup U] [LinearOrder U] [IsOrderedAddMonoid U] in
omit [AddCommGroup U] [IsOrderedAddMonoid U] in
lemma Auction.ReserveSecondPrice.bid_le_clearing_threshold_of_not_allocation_update_self
    (reserve : U) (b : I → U) (i : I) (bi : U)
    (hnot : allocation reserve (Function.update b i bi) ≠ some i) :
    bi ≤ max reserve (Auction.maxBidExcluding b i) := by
  let b' := Function.update b i bi
  by_cases hsell : reserve ≤ b' (SecondPrice.winner b')
  · have halloc : allocation reserve b' = some (SecondPrice.winner b') := by
      simp [allocation, hsell]
    have hwin_ne : SecondPrice.winner b' ≠ i := by
      intro h
      exact hnot (by simpa [b', h] using halloc)
    have hb_le_winner : b' i ≤ b' (SecondPrice.winner b') := by
      simpa [SecondPrice.winner] using Auction.bid_le_maxBid b' i
    have hmax_eq : Auction.maxBidExcluding b' i = Auction.maxBid b' := by
      exact Auction.maxBidExcluding_eq_maxBid_of_not_argmax b'
        (by simpa [SecondPrice.winner] using hwin_ne.symm)
    have hle_excluding' : bi ≤ Auction.maxBidExcluding b' i := by
      have hbid_winner_eq_max : b' (SecondPrice.winner b') = Auction.maxBid b' := by
        simpa [SecondPrice.winner] using Auction.argmaxBid_eq_maxBid b'
      rw [hmax_eq, ← hbid_winner_eq_max]
      simpa [b'] using hb_le_winner
    have hupdate : Auction.maxBidExcluding b' i = Auction.maxBidExcluding b i := by
      simpa [b'] using Auction.maxBidExcluding_update_self b i bi
    have hle_excluding : bi ≤ Auction.maxBidExcluding b i := by
      simpa [hupdate] using hle_excluding'
    exact le_trans hle_excluding (le_max_right reserve (Auction.maxBidExcluding b i))
  · have hbid_le_reserve : bi ≤ reserve := by
      have hb_le_winner : b' i ≤ b' (SecondPrice.winner b') := by
        simpa [SecondPrice.winner] using Auction.bid_le_maxBid b' i
      have hwinner_le_reserve : b' (SecondPrice.winner b') ≤ reserve :=
        le_of_lt (lt_of_not_ge hsell)
      simpa [b'] using le_trans hb_le_winner hwinner_le_reserve
    exact le_trans hbid_le_reserve (le_max_left reserve (Auction.maxBidExcluding b i))
