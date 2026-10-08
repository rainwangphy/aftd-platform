import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.AuctionReserveSecondPriceGame
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfersToStrategicGame
import AFTD.Kb.GameTheoryEconomics.AuctionReserveSecondPriceMechanism
import AFTD.Kb.GameTheoryEconomics.AuctionReserveSecondPriceUtility
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfers
import AFTD.Kb.GameTheoryEconomics.AuctionReserveSecondPriceAllocation
import AFTD.Kb.GameTheoryEconomics.AuctionReserveSecondPriceClearingPrice
import AFTD.Kb.GameTheoryEconomics.AuctionReserveSecondPriceMechanismAllocationRule
import AFTD.Kb.GameTheoryEconomics.AuctionReserveSecondPriceMechanismPaymentRule

/-!
# Auction.ReserveSecondPrice.game_eq_toStrategicGame

Topic: mechanism_design   Node: 113b6f538d65

Provenance: formalization of a published result. Source: EconCSLib, `Auction.ReserveSecondPrice.game_eq_toStrategicGame`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/ReserveVickrey.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`game reserve v` equals the strategic game induced by `mechanism reserve`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} [Fintype I] [Nontrivial I] [DecidableEq I] in
variable {U : Type*} [AddCommGroup U] [LinearOrder U] [IsOrderedAddMonoid U] in
variable {reserve : U} {v : I → U} in
omit [IsOrderedAddMonoid U] in
/-- `game reserve v` equals the strategic game induced by `mechanism reserve`. -/
lemma Auction.ReserveSecondPrice.game_eq_toStrategicGame (reserve : U) (v : I → U) :
    game reserve v =
      (mechanism reserve).toStrategicGame
        (fun (w : Option I) (pay : I → U) (vals : I → U) (i : I) =>
          if w = some i then vals i - pay i else 0)
        v := by
  unfold game mechanism MechanismWithTransfers.toStrategicGame
  congr 1
  funext b i
  simp [utility]
  split_ifs <;> rfl
