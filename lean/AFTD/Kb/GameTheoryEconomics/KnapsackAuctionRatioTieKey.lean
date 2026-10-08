import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.KnapsackAuction
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionRatio

/-!
# KnapsackAuction.ratioTieKey

Topic: mechanism_design   Node: c6598c319309

Provenance: formalization of a published result. Source: EconCSLib, `KnapsackAuction.ratioTieKey`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Knapsack.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Sorting key for the fractional greedy rule: higher ratio first, ties broken by the ambient linear order on `I`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open KnapsackAuction in
open scoped BigOperators in
variable {I : Type*} {U : Type*} [Field U] [LinearOrder U] [IsStrictOrderedRing U] in
variable [Fintype I] [DecidableEq I] [LinearOrder I] in
/-- Sorting key for the fractional greedy rule: higher ratio first, ties broken by the ambient linear order on `I`. -/
noncomputable def KnapsackAuction.ratioTieKey (A : KnapsackAuction I U) (b : I → U) (i : I) : U × I :=
  (-A.ratio b i, i)
