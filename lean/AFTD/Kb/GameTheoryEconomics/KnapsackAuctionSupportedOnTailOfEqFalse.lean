import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionBinaryAllocation
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionSupportedOn

/-!
# KnapsackAuction.supportedOn_tail_of_eq_false

Topic: mechanism_design   Node: 01ae3fa15425

Provenance: formalization of a published result. Source: EconCSLib, `KnapsackAuction.supportedOn_tail_of_eq_false`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Knapsack.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

KnapsackAuction.supportedOn_tail_of_eq_false
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators in
variable {I : Type*} [Fintype I] [DecidableEq I] in
omit [Fintype I] [DecidableEq I] in
lemma KnapsackAuction.supportedOn_tail_of_eq_false
    {i : I} {items : List I} {x : BinaryAllocation I}
    (hsupp : supportedOn (i :: items) x) (hxi : x i = false) :
    supportedOn items x := by
  intro j hj
  have hjmem : j ∈ i :: items := hsupp j hj
  rcases List.mem_cons.mp hjmem with rfl | hjtail
  · simp [hxi] at hj
  · exact hjtail
