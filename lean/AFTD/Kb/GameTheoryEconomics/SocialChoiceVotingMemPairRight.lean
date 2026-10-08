import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingPairSet

/-!
# SocialChoice.Voting.mem_pair_right

Topic: social_choice   Node: 0decf6468277

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.mem_pair_right`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/GibbardSatterthwaite.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SocialChoice.Voting.mem_pair_right
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N A : Type*} in
theorem SocialChoice.Voting.mem_pair_right (a b : A) : b ∈ pairSet a b :=
  Or.inr rfl
