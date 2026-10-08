import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.KnapsackAuction
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionBinaryAllocation
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionFeasibleBinaryAllocations
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionBinarySocialWelfare
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionFeasibleBinaryAllocationsNonempty
import AFTD.Kb.GameTheoryEconomics.ListExistsArgMaxOn
import AFTD.Kb.GameTheoryEconomics.ListArgMaxOn

/-!
# KnapsackAuction.exists_welfareMaximizer

Topic: mechanism_design   Node: fb5cdcaae8dd

Provenance: formalization of a published result. Source: EconCSLib, `KnapsackAuction.exists_welfareMaximizer`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Knapsack.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A welfare-maximizing feasible binary allocation, chosen using `List.argMaxOn` on the finite space of feasible `0/1` allocations.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open KnapsackAuction in
open scoped BigOperators in
variable {I : Type*} {U : Type*} [Field U] [LinearOrder U] [IsStrictOrderedRing U] in
variable [Fintype I] [DecidableEq I] in
/-- A welfare-maximizing feasible binary allocation, chosen using `List.argMaxOn` on the finite space of feasible `0/1` allocations. -/
lemma KnapsackAuction.exists_welfareMaximizer
    (A : KnapsackAuction I U) (b : I → U) (hW : 0 ≤ A.totalCapacity) :
    ∃ x : BinaryAllocation I,
      x ∈ A.feasibleBinaryAllocations ∧
        ∀ y ∈ A.feasibleBinaryAllocations,
          binarySocialWelfare b y ≤ binarySocialWelfare b x := by
  classical
  let xs := A.feasibleBinaryAllocations
  have hxs : xs ≠ [] := A.feasibleBinaryAllocations_nonempty hW
  cases h : xs with
  | nil =>
      exact False.elim (hxs h)
  | cons head tail =>
      obtain ⟨x, hxmem, hxmax⟩ := List.exists_argMax_on (binarySocialWelfare b) head tail
      refine ⟨x, ?_, ?_⟩
      · simpa [xs, h] using hxmem
      · intro y hy
        exact hxmax y (by simpa [xs, h] using hy)
