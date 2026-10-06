import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsDroopValidAssignment
import AFTD.Kb.GameTheoryEconomics.DroopMonroeScore
import AFTD.Kb.GameTheoryEconomics.IsDroopMonroeCommittee
import AFTD.Kb.GameTheoryEconomics.IsDroopEjrPlus
import AFTD.Kb.GameTheoryEconomics.IsDroopFjr
import AFTD.Kb.GameTheoryEconomics.DroopMonroeTieBallot
import AFTD.Kb.GameTheoryEconomics.DroopMonroeScoreLe

/-!
# droop_monroe_tie_violates_droop_ejr_plus_fjr

Topic: social_choice   Node: 88556ff5abe9

Provenance: original. Related work: answers the open Droop-EJR+ / Droop-FJR entries for Droop Monroe in Justified Representation: From Hare to Droop, arXiv:2508.00811, Table 1, negatively when ties are broken adversarially (n = 3, k = 2); whether some winning committee always satisfies them remains open

With ties, the Droop Monroe rule can output a committee violating Droop-EJR+ and Droop-FJR even when k + 1 divides n: n = 3, k = 2, ballots {0,1,3}, {0,1,3}, {0,2,3}, winning committee {1, 2}.
-/

/-- With ties, the Droop Monroe rule can output a committee that violates Droop-EJR+ and Droop-FJR even when `k + 1` divides `n`: three voters, `k = 2`, ballots {0,1,3}, {0,1,3}, {0,2,3}; every committee scores 2, and `W = {1, 2}` gives each voter only one approved member although all three jointly approve the two candidates 0 and 3. -/
theorem droop_monroe_tie_violates_droop_ejr_plus_fjr :
    (2 + 1) ∣ 3 ∧ is_droop_monroe_committee droop_monroe_tie_ballot 2 {1, 2} ∧
      ¬ is_droop_ejr_plus droop_monroe_tie_ballot 2 {1, 2} ∧
      ¬ is_droop_fjr droop_monroe_tie_ballot 2 {1, 2} := by
  refine ⟨by norm_num, ⟨![some 1, none, some 2], ?_, ?_⟩, ?_, ?_⟩
  · unfold is_droop_valid_assignment; decide
  · intro W' π' hv'
    have h := droop_monroe_score_le droop_monroe_tie_ballot 2 W' π' hv'
    have h2 : droop_monroe_score droop_monroe_tie_ballot ![some 1, none, some 2] = 2 := by
      unfold droop_monroe_score; decide
    rw [h2]; norm_num at h; omega
  · intro h
    obtain ⟨i, _, hi⟩ := h 2 (by norm_num) le_rfl Finset.univ (by simp)
      ⟨0, by decide, by decide⟩
    revert hi; revert i; decide
  · intro h
    obtain ⟨i, _, hi⟩ := h 2 (by norm_num) le_rfl {0, 3} Finset.univ (by decide) (by simp)
    revert hi; revert i; decide
