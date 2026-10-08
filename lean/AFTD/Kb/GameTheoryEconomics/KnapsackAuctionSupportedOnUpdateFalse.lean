import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionBinaryAllocation
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionSupportedOn

/-!
# KnapsackAuction.supportedOn_update_false

Topic: mechanism_design   Node: 23201e2e6a92

Provenance: formalization of a published result. Source: EconCSLib, `KnapsackAuction.supportedOn_update_false`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Knapsack.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

KnapsackAuction.supportedOn_update_false
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators in
variable {I : Type*} [Fintype I] [DecidableEq I] in
omit [Fintype I] in
lemma KnapsackAuction.supportedOn_update_false
    {i : I} {items : List I} {x : BinaryAllocation I}
    (hsupp : supportedOn (i :: items) x) :
    supportedOn items (Function.update x i false) := by
  intro j hj
  by_cases hji : j = i
  · subst hji
    simp at hj
  · have hxj : x j = true := by simpa [Function.update, hji] using hj
    have hjmem : j ∈ i :: items := hsupp j hxj
    rcases List.mem_cons.mp hjmem with rfl | hjtail
    · exact False.elim (hji rfl)
    · exact hjtail
