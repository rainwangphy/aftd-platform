import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionBinaryAllocation
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionNatBinarySocialWelfare

/-!
# KnapsackAuction.natBinarySocialWelfare_update_true_of_false

Topic: mechanism_design   Node: 1a565ccb48a5

Provenance: formalization of a published result. Source: EconCSLib, `KnapsackAuction.natBinarySocialWelfare_update_true_of_false`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Knapsack.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

KnapsackAuction.natBinarySocialWelfare_update_true_of_false
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators in
variable {I : Type*} [Fintype I] [DecidableEq I] in
lemma KnapsackAuction.natBinarySocialWelfare_update_true_of_false
    (b : I → Nat) {x : BinaryAllocation I} {i : I}
    (hxi : x i = false) :
    natBinarySocialWelfare b (Function.update x i true) =
      b i + natBinarySocialWelfare b x := by
  have htail :
      natBinarySocialWelfare b x =
        Finset.sum (Finset.univ.erase i) (fun j => if Function.update x i true j = true then b j else 0) := by
    rw [natBinarySocialWelfare, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
    have hs :
        Finset.sum (Finset.univ.erase i) (fun j => if x j = true then b j else 0) =
          Finset.sum (Finset.univ.erase i) (fun j => if Function.update x i true j = true then b j else 0) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      have hji : j ≠ i := by simpa using hj
      simp [Function.update, hji]
    simpa [hxi] using hs
  rw [natBinarySocialWelfare, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
  rw [htail]
  simp [Function.update]
