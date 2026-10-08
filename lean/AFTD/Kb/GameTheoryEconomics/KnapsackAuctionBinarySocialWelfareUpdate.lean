import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionBinaryAllocation
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionBinarySocialWelfare
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionBinaryToAllocation

/-!
# KnapsackAuction.binarySocialWelfare_update

Topic: mechanism_design   Node: 3cee10b1e595

Provenance: formalization of a published result. Source: EconCSLib, `KnapsackAuction.binarySocialWelfare_update`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Knapsack.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

KnapsackAuction.binarySocialWelfare_update
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators in
variable {I : Type*} {U : Type*} [Field U] [LinearOrder U] [IsStrictOrderedRing U] in
variable [Fintype I] [DecidableEq I] in
lemma KnapsackAuction.binarySocialWelfare_update
    (b : I → U) (i : I) (θ : U) (x : BinaryAllocation I) :
    binarySocialWelfare (Function.update b i θ) x =
      θ * binaryToAllocation x i +
        Finset.sum (Finset.univ.erase i) (fun j => b j * binaryToAllocation x j) := by
  have hsum :
      Finset.sum (Finset.univ.erase i) (fun j => Function.update b i θ j * binaryToAllocation x j) =
        Finset.sum (Finset.univ.erase i) (fun j => b j * binaryToAllocation x j) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hji : j ≠ i := by
      simpa using hj
    simp [Function.update, hji]
  cases hxi : x i with
  | false =>
      rw [binarySocialWelfare, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
      rw [hsum]
      simp [Function.update, binaryToAllocation, hxi]
  | true =>
      rw [binarySocialWelfare, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
      rw [hsum]
      simp [Function.update, binaryToAllocation, hxi]
