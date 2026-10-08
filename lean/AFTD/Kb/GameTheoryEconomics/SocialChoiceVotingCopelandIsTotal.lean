import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingIsTotal
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingCopeland
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingProfile
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingCopelandScore
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective

/-!
# SocialChoice.Voting.copeland_isTotal

Topic: social_choice   Node: 1d5a3fe718c7

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.copeland_isTotal`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/VotingRules.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SocialChoice.Voting.copeland_isTotal
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
open Finset in
open scoped BigOperators in
variable {N A : Type*} in
theorem SocialChoice.Voting.copeland_isTotal [Fintype N] [Fintype A] [Nonempty A] :
    IsTotal (N := N) (A := A) copeland := by
  intro P
  classical
  have hA : (Finset.univ : Finset A).Nonempty := Finset.univ_nonempty
  let scoreSet : Finset Int := Finset.univ.image (fun a => copelandScore P a)
  have hScore : scoreSet.Nonempty := hA.image _
  let maxScore : Int := scoreSet.max' hScore
  have hmem : maxScore ∈ scoreSet := Finset.max'_mem scoreSet hScore
  rcases Finset.mem_image.mp hmem with ⟨a, _, ha⟩
  refine ⟨a, ?_⟩
  simp [copeland, hA, scoreSet, maxScore, ha]
