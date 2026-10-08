import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingProfile
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingRelabelBallot

/-!
# SocialChoice.Voting.permuteCandidates

Topic: social_choice   Node: 3ef015450cf8

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.permuteCandidates`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Relabel candidates by applying the inverse permutation to each ballot.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
variable {N A : Type*} in
/-- Relabel candidates by applying the inverse permutation to each ballot. -/
noncomputable def SocialChoice.Voting.permuteCandidates [Fintype N] [Fintype A]
    (P : Profile N A) (σ : Equiv.Perm A) : Profile N A where
  pref := fun i => relabelBallot (P.pref i) σ.symm
