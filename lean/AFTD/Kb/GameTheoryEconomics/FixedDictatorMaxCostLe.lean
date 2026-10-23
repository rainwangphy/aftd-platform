import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TwoFacilityMaxCost
import AFTD.Kb.GameTheoryEconomics.TwoFacilityMaxCostNonneg
import AFTD.Kb.GameTheoryEconomics.FixedDictatorMaxCostLeOfSingletons
import AFTD.Kb.GameTheoryEconomics.IsFixedDictatorOutput
import AFTD.Kb.GameTheoryEconomics.IsTwoFacilityFeasible
import AFTD.Kb.GameTheoryEconomics.FixedDictatorMaxCostLeOfOneApproved
import AFTD.Kb.GameTheoryEconomics.IsClosestCandidate
import AFTD.Kb.GameTheoryEconomics.FixedDictatorMaxCostLeOfDoubleton

/-!
# fixed_dictator_max_cost_le

Topic: mechanism_design   Node: b9aaa01a2c24

Provenance: formalization of a published result. Source: scout/2610-18006-truthful-two-facility-location-with-candidate-locations-in.md:1341

On general metric spaces, in the two-facility location problem with candidate locations C and a finite nonempty set of n ≥ 2 agents with non-empty approval preferences p, every output w of the Fixed-Dictator mechanism satisfies two_facility_max_cost x p w ≤ 5 * two_facility_max_cost x p o for every feasible two-facility solution o; that is, the approximation ratio with respect to the max cost is at most 5.
-/

/-- Theorem 4.14 of arXiv:2610.18006: Fixed-Dictator achieves approximation ratio at most 5 for the max cost on general metric spaces. -/
theorem fixed_dictator_max_cost_le {ι X : Type*} [Fintype ι] [Nonempty ι] [MetricSpace X] [DecidableEq X]
    (C : Finset X) (x : ι → X) (p : ι → Fin 2 → Bool) (hp : ∀ i, p i 0 = true ∨ p i 1 = true)
    (hn : 2 ≤ Fintype.card ι) (w : Fin 2 → X) (hw : IsFixedDictatorOutput C x p w)
    (o : Fin 2 → X) (ho : IsTwoFacilityFeasible C o) :
    two_facility_max_cost x p w ≤ 5 * two_facility_max_cost x p o := by
  have hpos : 0 ≤ two_facility_max_cost x p o := two_facility_max_cost_nonneg x p o
  rcases hw with ⟨i, hi0, hi1, hw0, hw1⟩ | ⟨hnd, i, j, hi, hj, hw0, hw1⟩ | ⟨k, hk, i, hi, hwk, hwk'⟩
  · have h3 := fixed_dictator_max_cost_le_of_doubleton C x p w i hi0 hi1 hw0 hw1 o ho
    linarith
  · exact fixed_dictator_max_cost_le_of_singletons C x p hnd w i j hi hj hw0 hw1 o ho
  · have h3 := fixed_dictator_max_cost_le_of_one_approved C x p w k hk i hi hwk hwk' o ho
    linarith
