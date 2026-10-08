import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingProfile
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingPrefers
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective
import AFTD.Kb.GameTheoryEconomics.Profile

/-!
# SocialChoice.Voting.TopRank

Topic: social_choice   Node: 5db0d002a36b

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.TopRank`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Candidate `a` is top-ranked by voter `i`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
variable {N A : Type*} in
/-- Candidate `a` is top-ranked by voter `i`. -/
def SocialChoice.Voting.TopRank [Fintype N] [Fintype A] (P : Profile N A) (i : N) (a : A) : Prop :=
  ∀ b : A, b ≠ a → Prefers P i a b
