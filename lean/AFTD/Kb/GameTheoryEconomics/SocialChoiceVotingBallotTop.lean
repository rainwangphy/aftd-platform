import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefers
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective

/-!
# SocialChoice.Voting.BallotTop

Topic: social_choice   Node: f8976c29a416

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.BallotTop`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A linear-order ballot ranks `a` first.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
variable {N A : Type*} in
/-- A linear-order ballot ranks `a` first. -/
def SocialChoice.Voting.BallotTop (r : LinearOrder A) (a : A) : Prop :=
  ∀ b : A, b ≠ a → BallotPrefers r a b
