import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingFinThreeRankOrder
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingProfile

/-!
# SocialChoice.Voting.condorcetCycleProfile

Topic: social_choice   Node: 13340c6f7f98

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.condorcetCycleProfile`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/VotingRules.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The standard Condorcet cycle profile: voter 0 ranks `0 > 1 > 2`, voter 1 ranks `1 > 2 > 0`, and voter 2 ranks `2 > 0 > 1`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
open Finset in
open scoped BigOperators in
variable {N A : Type*} in
/-- The standard Condorcet cycle profile: voter 0 ranks `0 > 1 > 2`, voter 1 ranks `1 > 2 > 0`, and voter 2 ranks `2 > 0 > 1`. -/
noncomputable def SocialChoice.Voting.condorcetCycleProfile : Profile (Fin 3) (Fin 3) where
  pref
    | 0 => finThreeRankOrder
        (fun a => if a = 0 then 0 else if a = 1 then 1 else 2)
        (by intro a b h; fin_cases a <;> fin_cases b <;> simp at h ⊢)
    | 1 => finThreeRankOrder
        (fun a => if a = 1 then 0 else if a = 2 then 1 else 2)
        (by intro a b h; fin_cases a <;> fin_cases b <;> simp at h ⊢)
    | 2 => finThreeRankOrder
        (fun a => if a = 2 then 0 else if a = 0 then 1 else 2)
        (by intro a b h; fin_cases a <;> fin_cases b <;> simp at h ⊢)
