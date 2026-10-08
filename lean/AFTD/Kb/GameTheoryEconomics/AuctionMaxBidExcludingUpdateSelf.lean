import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AuctionMaxBidExcluding

/-!
# Auction.maxBidExcluding_update_self

Topic: mechanism_design   Node: 15d82c93e352

Provenance: formalization of a published result. Source: EconCSLib, `Auction.maxBidExcluding_update_self`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/AuctionBasic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Changing `i`'s bid does not affect the highest bid among the others.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} [Fintype I] [Nontrivial I] {V : Type*} [LinearOrder V] in
variable (b : I → V) in
variable [DecidableEq I] in
/-- Changing `i`'s bid does not affect the highest bid among the others. -/
lemma Auction.maxBidExcluding_update_self (i : I) (bi : V) :
    maxBidExcluding (Function.update b i bi) i = maxBidExcluding b i := by
  apply Finset.sup'_congr _ rfl
  intro j hj
  simp [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
