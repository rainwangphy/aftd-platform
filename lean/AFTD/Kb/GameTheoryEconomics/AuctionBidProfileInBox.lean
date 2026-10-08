import AFTD.Prelude
import AFTD.Kb.Tcs.V

/-!
# Auction.BidProfile.InBox

Topic: mechanism_design   Node: 17e7cc80d603

Provenance: formalization of a published result. Source: EconCSLib, `Auction.BidProfile.InBox`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/AuctionBasic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Each bid lies in the per-agent box $[\ell_i, u_i]$. $\forall i.\; \ell_i \le b_i \le u_i$.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I V : Type*} in
/-- Each bid lies in the per-agent box $[\ell_i, u_i]$. $\forall i.\; \ell_i \le b_i \le u_i$. -/
def Auction.BidProfile.InBox [LE V] (b : I → V) (ℓ u : I → V) : Prop :=
  ∀ i, ℓ i ≤ b i ∧ b i ≤ u i
