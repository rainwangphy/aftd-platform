import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionIsSingleItemAllocationRule

/-!
# BayesianSingleItemAuction.IsSingleItemAllocationRule.le_one

Topic: mechanism_design   Node: 7319cd1c32a8

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.IsSingleItemAllocationRule.le_one`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/OptimalSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A feasible single-item allocation gives each bidder probability at most `1`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators in
open MeasureTheory in
variable {I : Type*} in
/-- A feasible single-item allocation gives each bidder probability at most `1`. -/
theorem BayesianSingleItemAuction.IsSingleItemAllocationRule.le_one
    [Fintype I] [DecidableEq I] {x : (I → ℝ) → I → ℝ}
    (hx : IsSingleItemAllocationRule x) (b : I → ℝ) (i : I) :
    x b i ≤ 1 := by
  have hle_sum : x b i ≤ ∑ j, x b j := by
    exact Finset.single_le_sum (fun j _ => hx.1 b j) (Finset.mem_univ i)
  exact le_trans hle_sum (hx.2 b)
