import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfers
import AFTD.Kb.GameTheoryEconomics.AuctionFirstPriceWinner

/-!
# Auction.FirstPrice.mechanism

Topic: mechanism_design   Node: 5a8f53f103c3

Provenance: formalization of a published result. Source: EconCSLib, `Auction.FirstPrice.mechanism`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/FirstPrice.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The first-price auction as a `MechanismWithTransfers`. Agents report bids in `U` (their type space is homogeneous: `T i = U`). - Allocation: the winner index (element of `I`) - Payments: the winner pays their own bid `b i`; all losers pay `0`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} [Fintype I] [Nontrivial I] [DecidableEq I] in
variable {U : Type*} [AddCommGroup U] [LinearOrder U] [IsOrderedAddMonoid U] in
variable {v : I → U} in
/-- The first-price auction as a `MechanismWithTransfers`. Agents report bids in `U` (their type space is homogeneous: `T i = U`). - Allocation: the winner index (element of `I`) - Payments: the winner pays their own bid `b i`; all losers pay `0`. -/
noncomputable def Auction.FirstPrice.mechanism : MechanismWithTransfers I (fun _ => U) I U where
  allocationRule b := winner b
  paymentRule b i := if i = winner b then b i else 0
