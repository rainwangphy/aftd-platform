import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefers
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingAcyclicBallot
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBetweenBallotXy
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingDefaultBallot
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBetweenBallotYz
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective

/-!
# SocialChoice.Voting.acyclicBallot_spec

Topic: social_choice   Node: 6d6bb72985d6

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.acyclicBallot_spec`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Decisive.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SocialChoice.Voting.acyclicBallot_spec
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N A : Type*} in
theorem SocialChoice.Voting.acyclicBallot_spec [Fintype A]
    {x y z : A} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    BallotPrefers (acyclicBallot A hxy hxz hyz) x y ∧
      BallotPrefers (acyclicBallot A hxy hxz hyz) y z := by
  exact ⟨betweenBallot_xy (defaultBallot A) hxy hxz hyz,
    betweenBallot_yz (defaultBallot A) hxy hxz hyz⟩
