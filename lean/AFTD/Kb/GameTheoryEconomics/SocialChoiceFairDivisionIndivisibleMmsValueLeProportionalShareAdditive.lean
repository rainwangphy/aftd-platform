import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAdditiveValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleIsAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleMmsValue
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAdditiveValuationToValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleMmsValueLeOfForall

/-!
# SocialChoice.FairDivision.Indivisible.mmsValue_le_proportional_share_additive

Topic: fair_division   Node: 5b9f8d420b0d

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Indivisible.mmsValue_le_proportional_share_additive`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Indivisible/MMS.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

For additive valuations, the MMS value is at most the proportional share: `n * mmsValue ≤ v_i(allGoods)`. *Proof*: For any complete `B`, `min_j v_i(B_j) ≤ avg_j v_i(B_j) = v_i(allGoods)/n` (minimum ≤ average). Since this bound holds for every `B`, it holds for the supremum `mmsValue = sup_B min_j v_i(B_j)`. Uses `mmsValue_le_of_forall`. `i : N` guarantees `Fintype.card N ≥ 1`, so division by `n` is safe. [Budish 2011]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
variable {N G : Type*} in
variable [Fintype N] [DecidableEq G] in
/-- For additive valuations, the MMS value is at most the proportional share: `n * mmsValue ≤ v_i(allGoods)`. *Proof*: For any complete `B`, `min_j v_i(B_j) ≤ avg_j v_i(B_j) = v_i(allGoods)/n` (minimum ≤ average). Since this bound holds for every `B`, it holds for the supremum `mmsValue = sup_B min_j v_i(B_j)`. Uses `mmsValue_le_of_forall`. `i : N` guarantees `Fintype.card N ≥ 1`, so division by `n` is safe. [Budish 2011] -/
lemma SocialChoice.FairDivision.Indivisible.mmsValue_le_proportional_share_additive
    (w : AdditiveValuation N G)
    (allGoods : Finset G) (i : N)
    (hne : Nonempty {A : Allocation N G // IsAllocation allGoods A}) :
    (Fintype.card N : ℝ) * mmsValue w.toValuation allGoods i ≤
      w.toValuation.val i allGoods := by
  have hn_pos : (0 : ℝ) < Fintype.card N :=
    Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨i⟩)
  have hmms_bound : mmsValue w.toValuation allGoods i ≤
      w.toValuation.val i allGoods / (Fintype.card N : ℝ) := by
    apply mmsValue_le_of_forall w.toValuation allGoods i hne
    intro B hB
    rw [le_div_iff₀ hn_pos]
    calc iInf (fun j : N => w.toValuation.val i (B j)) * (Fintype.card N : ℝ)
        = (Fintype.card N : ℝ) * iInf (fun j : N => w.toValuation.val i (B j)) :=
            mul_comm _ _
      _ = ∑ _j : N, iInf (fun j' : N => w.toValuation.val i (B j')) := by
            simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ ∑ j : N, w.toValuation.val i (B j) :=
            Finset.sum_le_sum (fun j _ => Finite.ciInf_le _ j)
      _ = w.toValuation.val i allGoods := by
            simp only [AdditiveValuation.toValuation]
            rw [hB.complete, Finset.sum_biUnion (fun a _ b _ hab => hB.disjoint a b hab)]
  calc (Fintype.card N : ℝ) * mmsValue w.toValuation allGoods i
      ≤ (Fintype.card N : ℝ) * (w.toValuation.val i allGoods / (Fintype.card N : ℝ)) :=
          mul_le_mul_of_nonneg_left hmms_bound (le_of_lt hn_pos)
    _ = w.toValuation.val i allGoods := by field_simp
