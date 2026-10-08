import AFTD.Prelude

/-!
# KnapsackAuction.realBidOfNat

Topic: mechanism_design   Node: a35a1d82c7a4

Provenance: formalization of a published result. Source: EconCSLib, `KnapsackAuction.realBidOfNat`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Knapsack.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Natural-number bids viewed as real-valued bids.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators in
variable {I : Type*} [Fintype I] [DecidableEq I] [LinearOrder I] [Nonempty I] in
/-- Natural-number bids viewed as real-valued bids. -/
def KnapsackAuction.realBidOfNat (b : I → Nat) : I → ℝ :=
  fun i => (b i : ℝ)
