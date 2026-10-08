import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfers
import AFTD.Kb.GameTheoryEconomics.AuctionSecondPriceWinner
import AFTD.Kb.GameTheoryEconomics.AuctionSecondPriceSecondPrice

/-!
# Auction.SecondPrice.mechanism

Topic: mechanism_design   Node: 394156085d6d

Provenance: formalization of a published result. Source: EconCSLib, `Auction.SecondPrice.mechanism`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Vickrey.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The second-price auction as a `MechanismWithTransfers`. Agents report bids in `U` (their type space is homogeneous: `T i = U`). - Allocation: the winner index (element of `I`) - Payments: the winner pays `secondPrice b`; all losers pay `0`. This is the canonical `MechanismWithTransfers` instance from which the strategic game and DSIC statement are derived. [AGT Ch. 9]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} [Fintype I] [Nontrivial I] [DecidableEq I] in
variable {U : Type*} [AddCommGroup U] [LinearOrder U] [IsOrderedAddMonoid U] in
variable {v : I → U} in
/-- The second-price auction as a `MechanismWithTransfers`. Agents report bids in `U` (their type space is homogeneous: `T i = U`). - Allocation: the winner index (element of `I`) - Payments: the winner pays `secondPrice b`; all losers pay `0`. This is the canonical `MechanismWithTransfers` instance from which the strategic game and DSIC statement are derived. [AGT Ch. 9] -/
noncomputable def Auction.SecondPrice.mechanism : MechanismWithTransfers I (fun _ => U) I U where
  allocationRule b := winner b
  paymentRule b i := if i = winner b then secondPrice b else 0
