import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAdditiveValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAdditiveValuationToValuation
import AFTD.Kb.Tcs.G
import AFTD.Kb.Tcs.Weight

/-!
# SocialChoice.FairDivision.Indivisible.agent0_efx

Topic: fair_division   Node: 671dbfc53ef2

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Indivisible.agent0_efx`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Indivisible/EFX.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SocialChoice.FairDivision.Indivisible.agent0_efx
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
variable {N G : Type*} in
lemma SocialChoice.FairDivision.Indivisible.agent0_efx [DecidableEq G]
    (w : AdditiveValuation (Fin 2) G) (hnn₀ : ∀ g, 0 ≤ w.weight 0 g)
    (allGoods S_star : Finset G)
    (hfeas : w.toValuation.val 0 (allGoods \ S_star) ≤ w.toValuation.val 0 S_star)
    (g : G) :
    w.toValuation.val 0 ((allGoods \ S_star) \ {g}) ≤ w.toValuation.val 0 S_star := by
  exact le_trans ( Finset.sum_le_sum_of_subset_of_nonneg ( by aesop ) fun _ _ _ => hnn₀ _ ) hfeas
