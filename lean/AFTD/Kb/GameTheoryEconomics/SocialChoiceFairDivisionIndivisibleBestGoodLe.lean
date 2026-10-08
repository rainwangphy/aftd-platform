import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleBestGood
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAdditiveInstanceToAdditiveValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleRawBestGoodLe
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAdditiveInstance

/-!
# SocialChoice.FairDivision.Indivisible.bestGood_le

Topic: fair_division   Node: bb83a82ce526

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Indivisible.bestGood_le`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Indivisible/RoundRobin.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Every candidate good has no larger weight than `bestGood`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {n : ℕ} {G : Type*} in
variable [NeZero n] in
omit [NeZero n] in
/-- Every candidate good has no larger weight than `bestGood`. -/
lemma SocialChoice.FairDivision.Indivisible.bestGood_le [DecidableEq G]
    (I : AdditiveInstance (Fin n) G) (i : Fin n)
    (s : Finset G) (hs : s.Nonempty) {g : G} (hg : g ∈ s) :
    I.weight i g ≤ I.weight i (bestGood I i s hs) :=
  rawBestGood_le I.toAdditiveValuation i s hs hg
