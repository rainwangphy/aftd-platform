import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionBinaryAllocation
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionNatBinaryLoad

/-!
# KnapsackAuction.natBinaryLoad_eq_add_of_true

Topic: mechanism_design   Node: a90f4dc7720c

Provenance: formalization of a published result. Source: EconCSLib, `KnapsackAuction.natBinaryLoad_eq_add_of_true`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Knapsack.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

KnapsackAuction.natBinaryLoad_eq_add_of_true
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators in
variable {I : Type*} [Fintype I] [DecidableEq I] in
lemma KnapsackAuction.natBinaryLoad_eq_add_of_true
    (w : I → Nat) {x : BinaryAllocation I} {i : I}
    (hxi : x i = true) :
    natBinaryLoad w x =
      w i + natBinaryLoad w (Function.update x i false) := by
  have htail :
      natBinaryLoad w (Function.update x i false) =
        Finset.sum (Finset.univ.erase i) (fun j => if x j = true then w j else 0) := by
    rw [natBinaryLoad, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
    have hs :
        Finset.sum (Finset.univ.erase i) (fun j => if Function.update x i false j = true then w j else 0) =
          Finset.sum (Finset.univ.erase i) (fun j => if x j = true then w j else 0) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      have hji : j ≠ i := by simpa using hj
      simp [Function.update, hji]
    simpa [Function.update] using hs
  rw [natBinaryLoad, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
  rw [htail]
  simp [hxi]
