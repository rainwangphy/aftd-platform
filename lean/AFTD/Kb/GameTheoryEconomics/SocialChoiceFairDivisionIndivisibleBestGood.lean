import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAdditiveInstanceToAdditiveValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAdditiveInstance
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleRawBestGood

/-!
# SocialChoice.FairDivision.Indivisible.bestGood

Topic: fair_division   Node: 6a9c886ecb14

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Indivisible.bestGood`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Indivisible/RoundRobin.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`bestGood I i s hs` is a good in `s` maximizing agent `i`'s item weight.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {n : ℕ} {G : Type*} in
variable [NeZero n] in
/-- `bestGood I i s hs` is a good in `s` maximizing agent `i`'s item weight. -/
noncomputable def SocialChoice.FairDivision.Indivisible.bestGood [DecidableEq G]
    (I : AdditiveInstance (Fin n) G) (i : Fin n)
    (s : Finset G) (hs : s.Nonempty) : G :=
  rawBestGood I.toAdditiveValuation i s hs
