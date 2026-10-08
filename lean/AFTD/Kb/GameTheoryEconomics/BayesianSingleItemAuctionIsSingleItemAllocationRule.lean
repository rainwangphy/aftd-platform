import AFTD.Prelude

/-!
# BayesianSingleItemAuction.IsSingleItemAllocationRule

Topic: mechanism_design   Node: 006df6cd95f3

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.IsSingleItemAllocationRule`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/OptimalSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A nonnegative fractional allocation rule with total mass at most `1`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators in
open MeasureTheory in
variable {I : Type*} in
/-- A nonnegative fractional allocation rule with total mass at most `1`. -/
def BayesianSingleItemAuction.IsSingleItemAllocationRule [Fintype I]
    (x : (I → ℝ) → I → ℝ) : Prop :=
  (∀ b i, 0 ≤ x b i) ∧ ∀ b, (∑ i, x b i) ≤ 1
