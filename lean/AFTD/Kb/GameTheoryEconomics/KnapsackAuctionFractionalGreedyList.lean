import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.KnapsackAuction
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.Weight

/-!
# KnapsackAuction.fractionalGreedyList

Topic: mechanism_design   Node: d9692d771d90

Provenance: formalization of a published result. Source: EconCSLib, `KnapsackAuction.fractionalGreedyList`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Knapsack.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Greedy fractional allocation along a fixed list order. If the next item does not fully fit, the algorithm takes exactly the remaining fraction and halts.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators in
variable {I : Type*} {U : Type*} [Field U] [LinearOrder U] [IsStrictOrderedRing U] in
variable [Fintype I] [DecidableEq I] [LinearOrder I] in
/-- Greedy fractional allocation along a fixed list order. If the next item does not fully fit, the algorithm takes exactly the remaining fraction and halts. -/
noncomputable def KnapsackAuction.fractionalGreedyList (A : KnapsackAuction I U) (b : I → U) :
    List I → U → I → U
  | [], _ => fun _ => 0
  | i :: items, remaining =>
      if _ : remaining ≤ 0 then
        fun _ => 0
      else if _ : A.weight i ≤ remaining then
        Function.update (fractionalGreedyList A b items (remaining - A.weight i)) i 1
      else
        fun j => if j = i then remaining / A.weight i else 0
termination_by items _ => items.length
