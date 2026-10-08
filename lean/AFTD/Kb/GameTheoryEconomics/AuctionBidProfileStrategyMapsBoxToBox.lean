import AFTD.Prelude
import AFTD.Kb.Tcs.V

/-!
# Auction.BidProfile.StrategyMapsBoxToBox

Topic: mechanism_design   Node: 0909e8491921

Provenance: formalization of a published result. Source: EconCSLib, `Auction.BidProfile.StrategyMapsBoxToBox`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/AuctionBasic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A scalar strategy maps the input bid interval $[\ell, u]$ into $[\ell', u']$. Captures Lipschitz/contraction conditions for best-response dynamics in bounded auctions.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I V : Type*} in
/-- A scalar strategy maps the input bid interval $[\ell, u]$ into $[\ell', u']$. Captures Lipschitz/contraction conditions for best-response dynamics in bounded auctions. -/
def Auction.BidProfile.StrategyMapsBoxToBox [LE V] (σ : V → V) (ℓ u ℓ' u' : V) : Prop :=
  ∀ v, ℓ ≤ v ∧ v ≤ u → ℓ' ≤ σ v ∧ σ v ≤ u'
