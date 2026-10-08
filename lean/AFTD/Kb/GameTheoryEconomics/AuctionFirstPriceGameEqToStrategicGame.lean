import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.AuctionFirstPriceGame
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfersToStrategicGame
import AFTD.Kb.GameTheoryEconomics.AuctionFirstPriceMechanism
import AFTD.Kb.GameTheoryEconomics.AuctionFirstPriceUtility
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfers
import AFTD.Kb.GameTheoryEconomics.AuctionFirstPriceWinner
import AFTD.Kb.GameTheoryEconomics.AuctionArgmaxBid

/-!
# Auction.FirstPrice.game_eq_toStrategicGame

Topic: mechanism_design   Node: 3931a38f3e20

Provenance: formalization of a published result. Source: EconCSLib, `Auction.FirstPrice.game_eq_toStrategicGame`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/FirstPrice.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

`game v` equals the strategic game induced by `mechanism`. The payoffs agree because `paymentRule b i = if i = winner b then b i else 0`, so the utility is `v i - b i` for the winner and `0` for losers.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Auction Auction.FirstPrice in
variable {I : Type*} [Fintype I] [Nontrivial I] [DecidableEq I] in
variable {U : Type*} [AddCommGroup U] [LinearOrder U] [IsOrderedAddMonoid U] in
variable {v : I → U} in
omit [IsOrderedAddMonoid U] in
/-- `game v` equals the strategic game induced by `mechanism`. The payoffs agree because `paymentRule b i = if i = winner b then b i else 0`, so the utility is `v i - b i` for the winner and `0` for losers. -/
lemma Auction.FirstPrice.game_eq_toStrategicGame (v : I → U) :
    game v = mechanism.toStrategicGame
      (fun (w : I) (pay : I → U) (vals : I → U) (i : I) => if i = w then vals i - pay i else 0)
      v := by
  unfold game mechanism MechanismWithTransfers.toStrategicGame
  congr 1
  funext b i
  simp [utility, winner]
  split_ifs <;> simp_all
