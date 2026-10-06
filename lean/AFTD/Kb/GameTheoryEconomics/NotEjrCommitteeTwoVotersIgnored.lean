import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsEjrCommittee
import AFTD.Kb.GameTheoryEconomics.IsEjrCohesiveGroup

/-!
# not_ejr_committee_two_voters_ignored

Topic: social_choice   Node: 9edf8df58e18

Provenance: helper lemma. sanity check of is_ejr_committee

If two voters both approve only candidate 0, the committee {1} of size 1 violates EJR.
-/

theorem not_ejr_committee_two_voters_ignored : ¬ is_ejr_committee (n := 2) (m := 2) ![{0}, {0}] 1 {1} := by
  rintro ⟨-, h⟩
  obtain ⟨i, hi, hl⟩ := h 1 le_rfl {0, 1} (by unfold is_ejr_cohesive_group; decide)
  revert hl; revert hi; revert i; decide
