import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotFromInjective
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective

/-!
# SocialChoice.Voting.relabelBallot

Topic: social_choice   Node: ab2c5b2836b9

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.relabelBallot`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Relabel a linear order along a permutation of alternatives.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
variable {N A : Type*} in
/-- Relabel a linear order along a permutation of alternatives. -/
noncomputable def SocialChoice.Voting.relabelBallot (r : LinearOrder A) (σ : Equiv.Perm A) : LinearOrder A := by
  classical
  exact ballotFromInjective r σ σ.injective
