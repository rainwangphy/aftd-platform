import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingProfile
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingMajorityPrefers
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective
import AFTD.Kb.GameTheoryEconomics.Profile

/-!
# SocialChoice.Voting.copelandScore

Topic: social_choice   Node: e3973850badd

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.copelandScore`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/VotingRules.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Copeland score: pairwise majority wins minus pairwise majority losses.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
open Finset in
open scoped BigOperators in
variable {N A : Type*} in
/-- Copeland score: pairwise majority wins minus pairwise majority losses. -/
noncomputable def SocialChoice.Voting.copelandScore [Fintype N] [Fintype A]
    (P : Profile N A) (a : A) : Int :=
  Int.ofNat (Finset.card (Finset.univ.filter (fun b => MajorityPrefers P a b))) -
    Int.ofNat (Finset.card (Finset.univ.filter (fun b => MajorityPrefers P b a)))
