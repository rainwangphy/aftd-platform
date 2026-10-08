import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingVotingRule
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingUnanimity
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingMonotonicity
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingProfile
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingPrefers
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective
import AFTD.Kb.GameTheoryEconomics.Strict
import AFTD.Kb.GameTheoryEconomics.Profile

/-!
# SocialChoice.Voting.unanimous_strict_pref_not_chosen

Topic: social_choice   Node: 8a4e9c17b559

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.unanimous_strict_pref_not_chosen`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/GibbardSatterthwaite.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

If every voter strictly prefers `a` to `b`, then a unanimous monotonic resolute voting rule cannot choose `b`. This is the set-valued strict-profile form of [MSZ 21.32].
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N A : Type*} in
/-- If every voter strictly prefers `a` to `b`, then a unanimous monotonic resolute voting rule cannot choose `b`. This is the set-valued strict-profile form of [MSZ 21.32]. -/
theorem SocialChoice.Voting.unanimous_strict_pref_not_chosen [Fintype N] [Nonempty N] [Fintype A]
    (f : VotingRule N A) (hU : Unanimity f) (_hM : Monotonicity f)
    (P : Profile N A) {a b : A}
    (hab : ∀ i : N, Prefers P i a b) :
    b ∉ f P := by
  exact hU P a b hab
