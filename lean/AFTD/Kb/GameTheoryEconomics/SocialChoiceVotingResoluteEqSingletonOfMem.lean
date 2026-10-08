import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingVotingRule
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingResolute
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingProfile
import AFTD.Kb.GameTheoryEconomics.Profile

/-!
# SocialChoice.Voting.resolute_eq_singleton_of_mem

Topic: social_choice   Node: eebb30d9823e

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.resolute_eq_singleton_of_mem`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/GibbardSatterthwaite.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SocialChoice.Voting.resolute_eq_singleton_of_mem
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N A : Type*} in
theorem SocialChoice.Voting.resolute_eq_singleton_of_mem [Fintype N] [Fintype A]
    {f : VotingRule N A} (hf_res : Resolute f) {P : Profile N A} {a : A}
    (ha : a ∈ f P) : f P = {a} := by
  rcases Finset.card_eq_one.mp (hf_res P) with ⟨b, hb⟩
  have hba : a = b := by
    simpa [hb] using ha
  simp [hb, hba]
