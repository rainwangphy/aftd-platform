import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AuctionMaxBid
import AFTD.Kb.Tcs.V

/-!
# Auction.exists_maxBid

Topic: mechanism_design   Node: e66a3841c18e

Provenance: formalization of a published result. Source: EconCSLib, `Auction.exists_maxBid`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/AuctionBasic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

There exists a bidder whose bid equals the highest bid.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} [Fintype I] [Nontrivial I] {V : Type*} [LinearOrder V] in
variable (b : I → V) in
/-- There exists a bidder whose bid equals the highest bid. -/
lemma Auction.exists_maxBid : ∃ i : I, b i = maxBid b := by
  obtain ⟨i, _, h2⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty b
  exact ⟨i, symm h2⟩
