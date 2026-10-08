import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MultiItemBundle

/-!
# CombinatorialAllocation

Topic: mechanism_design   Node: 269cb8e9f1df

Provenance: formalization of a published result. Source: EconCSLib, `CombinatorialAllocation`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/AuctionBasic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A multi-item allocation assigns each agent a bundle of items.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A multi-item allocation assigns each agent a bundle of items. -/
def CombinatorialAllocation (I : Type*) (k : ℕ) := I → MultiItemBundle k
