import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAdditiveInstance
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleBestGood
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleRawBestGoodMem
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAdditiveInstanceToAdditiveValuation

/-!
# SocialChoice.FairDivision.Indivisible.bestGood_mem

Topic: fair_division   Node: 6d527e882d07

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Indivisible.bestGood_mem`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Indivisible/RoundRobin.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`bestGood` lies in the candidate set.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {n : ℕ} {G : Type*} in
variable [NeZero n] in
omit [NeZero n] in
/-- `bestGood` lies in the candidate set. -/
lemma SocialChoice.FairDivision.Indivisible.bestGood_mem [DecidableEq G]
    (I : AdditiveInstance (Fin n) G) (i : Fin n)
    (s : Finset G) (hs : s.Nonempty) :
    bestGood I i s hs ∈ s :=
  rawBestGood_mem I.toAdditiveValuation i s hs
