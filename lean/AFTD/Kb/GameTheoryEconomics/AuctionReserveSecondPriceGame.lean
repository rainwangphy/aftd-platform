import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AuctionReserveSecondPriceUtility
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame

/-!
# Auction.ReserveSecondPrice.game

Topic: mechanism_design   Node: 740b65f92280

Provenance: formalization of a published result. Source: EconCSLib, `Auction.ReserveSecondPrice.game`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/ReserveVickrey.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Reserve second-price auction as a strategic game.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} [Fintype I] [Nontrivial I] [DecidableEq I] in
variable {U : Type*} [AddCommGroup U] [LinearOrder U] [IsOrderedAddMonoid U] in
variable {reserve : U} {v : I → U} in
/-- Reserve second-price auction as a strategic game. -/
noncomputable def Auction.ReserveSecondPrice.game (reserve : U) (v : I → U) : EconCSLib.StrategicGame I U where
  strategy := fun _ => U
  payoff b i := utility reserve v b i
