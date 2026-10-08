import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefers
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective

/-!
# SocialChoice.Voting.BallotPrefers.asymm

Topic: social_choice   Node: c256d4b87330

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.BallotPrefers.asymm`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SocialChoice.Voting.BallotPrefers.asymm
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
variable {N A : Type*} in
theorem SocialChoice.Voting.BallotPrefers.asymm (r : LinearOrder A) {a b : A} :
    BallotPrefers r a b → ¬ BallotPrefers r b a := by
  intro hab hba
  have hle_not := (r.lt_iff_le_not_ge a b).mp hab
  have hle := (r.lt_iff_le_not_ge b a).mp hba |>.left
  exact hle_not.right hle
