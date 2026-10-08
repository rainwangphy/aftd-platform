import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AuctionBidProfileInBox
import AFTD.Kb.GameTheoryEconomics.AuctionBidProfileInSet

/-!
# Auction.BidProfile.inBox_iff_inSet_Icc

Topic: mechanism_design   Node: fd0c7b0f6ead

Provenance: formalization of a published result. Source: EconCSLib, `Auction.BidProfile.inBox_iff_inSet_Icc`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/AuctionBasic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`InBox b ℓ u` is equivalent to `InSet b (fun i => Set.Icc (ℓ i) (u i))`. Makes box-constrained bid spaces interoperable with the Mathlib `Set.Icc` API (continuity, compactness, integration).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I V : Type*} in
/-- `InBox b ℓ u` is equivalent to `InSet b (fun i => Set.Icc (ℓ i) (u i))`. Makes box-constrained bid spaces interoperable with the Mathlib `Set.Icc` API (continuity, compactness, integration). -/
lemma Auction.BidProfile.inBox_iff_inSet_Icc [Preorder V] (b : I → V) (ℓ u : I → V) :
    InBox b ℓ u ↔ InSet b (fun i => Set.Icc (ℓ i) (u i)) := by
  unfold InBox InSet
  simp [Set.mem_Icc]
