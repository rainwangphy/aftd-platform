import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.AuctionSecondPriceUtility
import AFTD.Kb.GameTheoryEconomics.StrategicGame

/-!
# Auction.SecondPrice.game

Topic: mechanism_design   Node: 722944349c32

Provenance: formalization of a published result. Source: EconCSLib, `Auction.SecondPrice.game`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Vickrey.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Second-price auction as a strategic game. This is also the game induced by `mechanism` via `MechanismWithTransfers.toStrategicGame`; see `game_eq_toStrategicGame`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} [Fintype I] [Nontrivial I] [DecidableEq I] in
variable {U : Type*} [AddCommGroup U] [LinearOrder U] [IsOrderedAddMonoid U] in
variable {v : I → U} in
/-- Second-price auction as a strategic game. This is also the game induced by `mechanism` via `MechanismWithTransfers.toStrategicGame`; see `game_eq_toStrategicGame`. -/
noncomputable def Auction.SecondPrice.game (v : I → U) : EconCSLib.StrategicGame I U where
  strategy := fun _ => U
  payoff b i := utility v b i
