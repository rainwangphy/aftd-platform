import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsFixedDictatorOutput
import AFTD.Kb.GameTheoryEconomics.FixedDictatorSocialCostLeOfDoubleton
import AFTD.Kb.GameTheoryEconomics.FixedDictatorSocialCostLeOfSingletons
import AFTD.Kb.GameTheoryEconomics.FixedDictatorSocialCostLeOfOneApproved
import AFTD.Kb.GameTheoryEconomics.TwoFacilitySocialCost
import AFTD.Kb.GameTheoryEconomics.IsTwoFacilityFeasible
import AFTD.Kb.GameTheoryEconomics.IsClosestCandidate

/-!
# fixed_dictator_social_cost_le

Topic: mechanism_design   Node: 463e3cc0d580

Provenance: formalization of a published result. Source: arXiv:2610.18006 (Truthful two-facility location with candidate locations in metric spaces), Theorem 4.5. Lean differs: holds for every choice of the fixed agents and every tie-breaking (IsFixedDictatorOutput), and is stated against every feasible o rather than as a ratio

On a general metric space, for n ≥ 2 agents with known non-empty approval preferences over two facilities and any candidate set C, every outcome w of Fixed-Dictator satisfies SC(w) ≤ (2n - 1) SC(o) for every feasible solution o; that is, its approximation ratio for the social cost is at most 2n - 1.
-/

theorem fixed_dictator_social_cost_le {ι X : Type*} [Fintype ι] [MetricSpace X] [DecidableEq X]
    (C : Finset X) (x : ι → X) (p : ι → Fin 2 → Bool) (hp : ∀ i, p i 0 = true ∨ p i 1 = true)
    (hn : 2 ≤ Fintype.card ι) (w : Fin 2 → X) (hw : IsFixedDictatorOutput C x p w)
    (o : Fin 2 → X) (ho : IsTwoFacilityFeasible C o) :
    two_facility_social_cost x p w ≤ (2 * (Fintype.card ι : ℝ) - 1) * two_facility_social_cost x p o := by
  rcases hw with ⟨i, hi0, hi1, hw0, hw1⟩ | ⟨hnd, i, j, hi, hj, hw0, hw1⟩ | ⟨k, hk, i, hi, hwk, hwk'⟩
  · exact fixed_dictator_social_cost_le_of_doubleton C x p w i hi0 hi1 hw0 hw1 o ho
  · exact fixed_dictator_social_cost_le_of_singletons C x p hnd w i j hi hj hw0 hw1 o ho
  · exact fixed_dictator_social_cost_le_of_one_approved C x p w k hk i hi hwk hwk' o ho
