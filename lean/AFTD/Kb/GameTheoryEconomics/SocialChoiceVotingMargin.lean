import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingVotersPreferring
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingProfile

/-!
# SocialChoice.Voting.margin

Topic: social_choice   Node: 49643c25a290

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.margin`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/VotingRules.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Pairwise majority margin: voters preferring `a` to `b` minus voters preferring `b` to `a`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
open Finset in
open scoped BigOperators in
variable {N A : Type*} in
/-- Pairwise majority margin: voters preferring `a` to `b` minus voters preferring `b` to `a`. -/
noncomputable def SocialChoice.Voting.margin [Fintype N] [Fintype A]
    (P : Profile N A) (a b : A) : Int :=
  Int.ofNat (Finset.card (votersPreferring P a b)) -
    Int.ofNat (Finset.card (votersPreferring P b a))
