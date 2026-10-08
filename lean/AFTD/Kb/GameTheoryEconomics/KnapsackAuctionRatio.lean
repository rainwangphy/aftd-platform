import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.KnapsackAuction

/-!
# KnapsackAuction.ratio

Topic: mechanism_design   Node: 93cb6c0eaa9d

Provenance: formalization of a published result. Source: EconCSLib, `KnapsackAuction.ratio`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Knapsack.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Value-to-weight ratio used by the fractional greedy rule.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators in
variable {I : Type*} {U : Type*} [Field U] [LinearOrder U] [IsStrictOrderedRing U] in
variable [Fintype I] [DecidableEq I] [LinearOrder I] in
/-- Value-to-weight ratio used by the fractional greedy rule. -/
noncomputable def KnapsackAuction.ratio (A : KnapsackAuction I U) (b : I → U) (i : I) : U :=
  b i / A.weight i
