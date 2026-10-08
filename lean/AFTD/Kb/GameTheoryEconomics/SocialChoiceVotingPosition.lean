import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingRank
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective

/-!
# SocialChoice.Voting.position

Topic: social_choice   Node: 8b8c07fa7c0f

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.position`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/VotingRules.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The 1-based position of `a` in ballot `r`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
open Finset in
open scoped BigOperators in
variable {N A : Type*} in
/-- The 1-based position of `a` in ballot `r`. -/
noncomputable def SocialChoice.Voting.position [Fintype A] (r : LinearOrder A) (a : A) : Nat :=
  rank r a + 1
