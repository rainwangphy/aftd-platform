import AFTD.Prelude

/-!
# KnapsackAuction.fractionalSupportedOn

Topic: mechanism_design   Node: aa338332bdaa

Provenance: formalization of a published result. Source: EconCSLib, `KnapsackAuction.fractionalSupportedOn`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Knapsack.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A real-valued allocation is supported on a list if every nonzero coordinate appears in that list.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators in
variable {I : Type*} [Fintype I] [DecidableEq I] [LinearOrder I] [Nonempty I] in
/-- A real-valued allocation is supported on a list if every nonzero coordinate appears in that list. -/
def KnapsackAuction.fractionalSupportedOn (items : List I) (x : I → ℝ) : Prop :=
  ∀ i, x i ≠ 0 → i ∈ items
