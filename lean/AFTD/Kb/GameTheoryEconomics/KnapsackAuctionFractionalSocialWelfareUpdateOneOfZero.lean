import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionFractionalSocialWelfare

/-!
# KnapsackAuction.fractionalSocialWelfare_update_one_of_zero

Topic: mechanism_design   Node: b5da9f45750c

Provenance: formalization of a published result. Source: EconCSLib, `KnapsackAuction.fractionalSocialWelfare_update_one_of_zero`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Knapsack.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

KnapsackAuction.fractionalSocialWelfare_update_one_of_zero
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators in
variable {I : Type*} [Fintype I] [DecidableEq I] [LinearOrder I] [Nonempty I] in
omit [LinearOrder I] [Nonempty I] in
lemma KnapsackAuction.fractionalSocialWelfare_update_one_of_zero
    (b : I → ℝ) {x : I → ℝ} {i : I}
    (hxi : x i = 0) :
    fractionalSocialWelfare b (Function.update x i 1) =
      b i + fractionalSocialWelfare b x := by
  rw [fractionalSocialWelfare, fractionalSocialWelfare,
    ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
  have hs :
      Finset.sum (Finset.univ.erase i) (fun j => b j * Function.update x i 1 j) =
        Finset.sum (Finset.univ.erase i) (fun j => b j * x j) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hji : j ≠ i := by simpa using hj
    simp [Function.update, hji]
  rw [hs]
  simp [Function.update, hxi]
