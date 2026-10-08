import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingTripartition
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingPrefers
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingCondorcetProfile
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingTripartitionLemma
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefers
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingAcyclicBallot
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingProfile
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingAcyclicBallotSpec
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective

/-!
# SocialChoice.Voting.condorcetProfile_spec

Topic: social_choice   Node: 289b9367a05b

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.condorcetProfile_spec`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Decisive.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SocialChoice.Voting.condorcetProfile_spec
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N A : Type*} in
theorem SocialChoice.Voting.condorcetProfile_spec [Fintype N] [Fintype A]
    {S T U : Set N}
    {x y z : A} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hSTU : tripartition S T U) :
    ∀ i,
      (i ∈ S → Prefers (condorcetProfile S T U x y z hxy hxz hyz) i x y ∧
          Prefers (condorcetProfile S T U x y z hxy hxz hyz) i y z) ∧
      (i ∈ T → Prefers (condorcetProfile S T U x y z hxy hxz hyz) i y z ∧
          Prefers (condorcetProfile S T U x y z hxy hxz hyz) i z x) ∧
      (i ∈ U → Prefers (condorcetProfile S T U x y z hxy hxz hyz) i z x ∧
          Prefers (condorcetProfile S T U x y z hxy hxz hyz) i x y) := by
  classical
  intro i
  have htri := tripartition_lemma hSTU i
  by_cases hS : i ∈ S
  · constructor
    · intro _
      simpa [condorcetProfile, Prefers, hS] using acyclicBallot_spec hxy hxz hyz
    constructor
    · intro hT
      exact False.elim ((htri.2.2.1.mp hT).1 hS)
    · intro hU
      exact False.elim ((htri.2.2.2.mp hU).1 hS)
  · by_cases hT : i ∈ T
    · have hnotU : i ∉ U := (htri.2.2.1.mp hT).2
      constructor
      · intro hS'
        exact False.elim (hS hS')
      constructor
      · intro _
        simpa [condorcetProfile, Prefers, hS, hT] using
          acyclicBallot_spec hyz (Ne.symm hxy) (Ne.symm hxz)
      · intro hU'
        exact False.elim (hnotU hU')
    · have hU : i ∈ U := by
        exact (htri.2.2.2).mpr ⟨hS, hT⟩
      constructor
      · intro hS'
        exact False.elim (hS hS')
      constructor
      · intro hT'
        exact False.elim (hT hT')
      · intro _
        simpa [condorcetProfile, Prefers, hS, hT] using
          acyclicBallot_spec (Ne.symm hxz) (Ne.symm hyz) hxy
