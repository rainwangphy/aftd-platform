import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingProfile
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingPrefers
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective
import AFTD.Kb.GameTheoryEconomics.Profile

/-!
# SocialChoice.Voting.SimpleLift

Topic: social_choice   Node: 747f2392cda9

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.SimpleLift`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`Q` is obtained from `P` by weakly raising `a`: anything below `a` in `P` remains below `a` in `Q`, and anything above `a` in `Q` was already above `a` in `P`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
variable {N A : Type*} in
variable [Fintype N] [Fintype A] in
/-- `Q` is obtained from `P` by weakly raising `a`: anything below `a` in `P` remains below `a` in `Q`, and anything above `a` in `Q` was already above `a` in `P`. -/
def SocialChoice.Voting.SimpleLift (Q P : Profile N A) (a : A) : Prop :=
  ∀ i x, (Prefers P i a x → Prefers Q i a x) ∧
    (Prefers Q i x a → Prefers P i x a)
