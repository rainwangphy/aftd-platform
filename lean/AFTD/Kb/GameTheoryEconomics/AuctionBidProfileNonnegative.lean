import AFTD.Prelude
import AFTD.Kb.Tcs.V

/-!
# Auction.BidProfile.Nonnegative

Topic: mechanism_design   Node: b389fa68994c

Provenance: formalization of a published result. Source: EconCSLib, `Auction.BidProfile.Nonnegative`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/AuctionBasic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Every bid is nonnegative. $\forall i.\; b_i \ge 0$. Captures the standard private-value convention that bids represent willingness-to-pay.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I V : Type*} in
/-- Every bid is nonnegative. $\forall i.\; b_i \ge 0$. Captures the standard private-value convention that bids represent willingness-to-pay. -/
def Auction.BidProfile.Nonnegative [Zero V] [LE V] (b : I → V) : Prop :=
  ∀ i, 0 ≤ b i
