import AFTD.Prelude

/-!
# KnapsackAuction.highestBidValue

Topic: mechanism_design   Node: 792f14443b3a

Provenance: formalization of a published result. Source: EconCSLib, `KnapsackAuction.highestBidValue`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Knapsack.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Highest single-item value.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators in
variable {I : Type*} [Fintype I] [DecidableEq I] [LinearOrder I] [Nonempty I] in
/-- Highest single-item value. -/
noncomputable def KnapsackAuction.highestBidValue (b : I → Nat) : Nat :=
  Finset.sup' Finset.univ Finset.univ_nonempty b
