import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionFractionalSocialWelfare
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionRealBidOfNat
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionNatFractionalGreedyList
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionNatBinarySocialWelfare
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionIntegralGreedyList
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionHighestBidValue
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionBinaryAllocation
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionEqZeroOfFractionalSupportedOnOfNotMem
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionNatFractionalGreedyListSupportedOn
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionEqFalseOfSupportedOnOfNotMem
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionIntegralGreedyListSupportedOn
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionNatBinarySocialWelfareUpdateTrueOfFalse
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionFractionalSocialWelfareUpdateOneOfZero
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionFractionalSocialWelfareSingleton
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionLeHighestBidValue
import AFTD.Kb.GameTheoryEconomics.KnapsackAuction

/-!
# KnapsackAuction.natFractionalGreedyList_le_integralGreedyList_plus_highest

Topic: mechanism_design   Node: bb51257bfc7b

Provenance: formalization of a published result. Source: EconCSLib, `KnapsackAuction.natFractionalGreedyList_le_integralGreedyList_plus_highest`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Knapsack.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

KnapsackAuction.natFractionalGreedyList_le_integralGreedyList_plus_highest
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open KnapsackAuction in
open scoped BigOperators in
variable {I : Type*} [Fintype I] [DecidableEq I] [LinearOrder I] [Nonempty I] in
omit [LinearOrder I] in
lemma KnapsackAuction.natFractionalGreedyList_le_integralGreedyList_plus_highest
    (w b : I → Nat) (hwpos : ∀ i, 0 < w i) :
    ∀ {items : List I}, items.Nodup → ∀ remaining,
      fractionalSocialWelfare (realBidOfNat b) (natFractionalGreedyList w items remaining) ≤
        (natBinarySocialWelfare b (integralGreedyList w items remaining) : ℝ) +
          highestBidValue b := by
  intro items hitems
  induction items with
  | nil =>
      intro remaining
      have hnil :
          (0 : ℝ) ≤
            (natBinarySocialWelfare b (fun _ => false) : ℝ) + highestBidValue b := by
        positivity
      simpa [natFractionalGreedyList, integralGreedyList, fractionalSocialWelfare] using hnil
  | cons i items ih =>
      intro remaining
      have hnotin : i ∉ items := (List.nodup_cons.mp hitems).1
      have htailNodup : items.Nodup := (List.nodup_cons.mp hitems).2
      by_cases hfit : w i ≤ remaining
      · have hfracTail :=
          ih htailNodup (remaining - w i)
        have hfracZero : natFractionalGreedyList w items (remaining - w i) i = 0 := by
          exact eq_zero_of_fractionalSupportedOn_of_not_mem
            (natFractionalGreedyList_supportedOn w items (remaining - w i)) hnotin
        have hintFalse : integralGreedyList w items (remaining - w i) i = false := by
          exact eq_false_of_supportedOn_of_not_mem
            (integralGreedyList_supportedOn w items (remaining - w i)) hnotin
        have hintEq :
            (natBinarySocialWelfare b (integralGreedyList w (i :: items) remaining) : ℝ) =
              (b i : ℝ) +
                natBinarySocialWelfare b (integralGreedyList w items (remaining - w i)) := by
          exact_mod_cast
            (show natBinarySocialWelfare b (integralGreedyList w (i :: items) remaining) =
                b i + natBinarySocialWelfare b (integralGreedyList w items (remaining - w i)) by
              simpa [integralGreedyList, hfit] using
                (natBinarySocialWelfare_update_true_of_false
                  (b := b) (x := integralGreedyList w items (remaining - w i)) (i := i) hintFalse))
        calc
          fractionalSocialWelfare (realBidOfNat b)
              (natFractionalGreedyList w (i :: items) remaining)
              = (b i : ℝ) +
                  fractionalSocialWelfare (realBidOfNat b)
                    (natFractionalGreedyList w items (remaining - w i)) := by
                  simp [natFractionalGreedyList, hfit]
                  simpa [realBidOfNat] using
                    (fractionalSocialWelfare_update_one_of_zero
                      (b := realBidOfNat b) (x := natFractionalGreedyList w items (remaining - w i))
                      (i := i) hfracZero)
          _ ≤ (b i : ℝ) +
                ((natBinarySocialWelfare b (integralGreedyList w items (remaining - w i)) : ℝ) +
                  highestBidValue b) := by
                simpa [add_assoc, add_left_comm, add_comm] using
                  add_le_add_right hfracTail (b i : ℝ)
          _ = (natBinarySocialWelfare b (integralGreedyList w (i :: items) remaining) : ℝ) +
                highestBidValue b := by
                rw [hintEq]
                ring
      · have hwipos : 0 < w i := hwpos i
        have hrem_le : remaining ≤ w i := Nat.le_of_lt (lt_of_not_ge hfit)
        have hratio_le_one : (remaining : ℝ) / w i ≤ 1 := by
          exact (div_le_one (by exact_mod_cast hwipos)).2 (by exact_mod_cast hrem_le)
        calc
          fractionalSocialWelfare (realBidOfNat b)
              (natFractionalGreedyList w (i :: items) remaining)
              = (b i : ℝ) * ((remaining : ℝ) / w i) := by
                  simp [natFractionalGreedyList, hfit]
                  simp [fractionalSocialWelfare_singleton, realBidOfNat]
          _ ≤ b i := by
              have hmul :
                  (b i : ℝ) * ((remaining : ℝ) / w i) ≤ (b i : ℝ) * 1 := by
                exact mul_le_mul_of_nonneg_left hratio_le_one (show 0 ≤ (b i : ℝ) by positivity)
              simpa using hmul
          _ ≤ highestBidValue b := by
              exact_mod_cast le_highestBidValue b i
          _ ≤ (natBinarySocialWelfare b (integralGreedyList w (i :: items) remaining) : ℝ) +
                highestBidValue b := by
              have hnonneg :
                  (0 : ℝ) ≤
                    (natBinarySocialWelfare b (integralGreedyList w (i :: items) remaining) : ℝ) := by
                positivity
              exact le_add_of_nonneg_left hnonneg
