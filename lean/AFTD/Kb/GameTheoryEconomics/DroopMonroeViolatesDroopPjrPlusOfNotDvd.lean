import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsDroopMonroeCommittee
import AFTD.Kb.GameTheoryEconomics.IsDroopPjrPlus
import AFTD.Kb.GameTheoryEconomics.DroopMonroeScoreLe
import AFTD.Kb.GameTheoryEconomics.IsDroopValidAssignment
import AFTD.Kb.GameTheoryEconomics.DroopMonroeScore

/-!
# droop_monroe_violates_droop_pjr_plus_of_not_dvd

Topic: social_choice   Node: 81a5a5c7920c

Provenance: formalization of a published result. Source: Justified Representation: From Hare to Droop, arXiv:2508.00811, Proposition 4: Droop Monroe does not satisfy Droop-PJR if k + 1 does not divide n, and Droop-PJR+ implies Droop-PJR. The rule's definitions follow arXiv:2508.00811 (Def. 11, Def. 16). This instance (four voters, k = 2) was found by the agents' Prover when it refuted droop_monroe_satisfies_droop_pjr_plus_general.

Without the assumption that k + 1 divides n, the Droop Monroe rule can output a committee violating Droop-PJR+: with n = 4 voters, k = 2 and ballots {1,3}, {1,3}, {3}, {2}, the committee {1, 2} is a Droop Monroe winner (a Droop-valid assignment scores 3, the most possible), but the group of the first three voters (2·4 < 3·3) jointly approves the unelected candidate 3 and collectively approves only one member of the committee.
-/

theorem droop_monroe_violates_droop_pjr_plus_of_not_dvd :
    ¬ (2 + 1) ∣ 4 ∧
      is_droop_monroe_committee (![{1, 3}, {1, 3}, {3}, {2}] : Fin 4 → Finset (Fin 4)) 2 {1, 2} ∧
      ¬ is_droop_pjr_plus (![{1, 3}, {1, 3}, {3}, {2}] : Fin 4 → Finset (Fin 4)) 2 {1, 2} := by
  refine ⟨by decide, ⟨![some 1, some 1, none, some 2], ?_, ?_⟩, ?_⟩
  · unfold is_droop_valid_assignment; decide
  · intro W' π' hv'
    have h := droop_monroe_score_le (![{1, 3}, {1, 3}, {3}, {2}] : Fin 4 → Finset (Fin 4)) 2 W'
      π' hv'
    have h2 : droop_monroe_score (![{1, 3}, {1, 3}, {3}, {2}] : Fin 4 → Finset (Fin 4))
        ![some 1, some 1, none, some 2] = 3 := by
      unfold droop_monroe_score; decide
    rw [h2]; norm_num at h; omega
  · intro h
    have := h 2 (by norm_num) le_rfl {0, 1, 2} (by decide) ⟨3, by decide, by decide⟩
    revert this; decide
