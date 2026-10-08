import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.KnapsackAuction
import AFTD.Kb.Tcs.Weight

/-!
# KnapsackAuction.size

Topic: mechanism_design   Node: 005db85a80f6

Provenance: formalization of a published result. Source: EconCSLib, `KnapsackAuction.size`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Knapsack.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Agent `i`'s public weight.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators in
variable {I : Type*} {U : Type*} [Field U] [LinearOrder U] [IsStrictOrderedRing U] in
/-- Agent `i`'s public weight. -/
abbrev KnapsackAuction.size (A : KnapsackAuction I U) (i : I) : U :=
  A.weight i
