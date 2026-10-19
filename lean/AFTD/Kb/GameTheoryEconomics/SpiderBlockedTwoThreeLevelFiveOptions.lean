import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiderGamma
import AFTD.Kb.GameTheoryEconomics.NatMexList
import AFTD.Kb.GameTheoryEconomics.SpiderRho
import AFTD.Kb.GameTheoryEconomics.SpiderLegEnd
import AFTD.Kb.GameTheoryEconomics.SpiderRhoStar
import AFTD.Kb.GameTheoryEconomics.SpiderUpdateCentre
import AFTD.Kb.GameTheoryEconomics.CentreStatus

/-!
# spider_blocked_two_three_level_five_options

Topic: combinatorial_games   Node: ea2f99418b0a

Provenance: helper lemma. step towards spider_blocked_two_three_level_five

One unfolding step of the recursion for the level-5 root state (none;{(5,inward),2^*,3^*}) at fuel n+1: the value is the mex of the list of the 19 options the recursion generates, where each option is a coefficient d (written as a numeral) xor spider_gamma at fuel n of the corresponding reduced position, in the exact order in which the recursion enumerates the legs, the cuts j and the two directions.
-/

/-- The 19-option list of the level-5 root state, at symbolic fuel n+1. -/
theorem spider_blocked_two_three_level_five_options (n : ℕ) :
    spider_gamma (n + 1) CentreStatus.none
        [(5, SpiderLegEnd.inward), (2, SpiderLegEnd.free), (3, SpiderLegEnd.free)] =
      nat_mex_list
        [ 0 ^^^ spider_gamma n CentreStatus.incoming [(2, SpiderLegEnd.free), (3, SpiderLegEnd.free)],
          1 ^^^ spider_gamma n CentreStatus.outgoing [(2, SpiderLegEnd.free), (3, SpiderLegEnd.free)],
          1 ^^^ spider_gamma n CentreStatus.none [(1, SpiderLegEnd.inward), (2, SpiderLegEnd.free), (3, SpiderLegEnd.free)],
          0 ^^^ spider_gamma n CentreStatus.none [(1, SpiderLegEnd.outward), (2, SpiderLegEnd.free), (3, SpiderLegEnd.free)],
          0 ^^^ spider_gamma n CentreStatus.none [(2, SpiderLegEnd.inward), (2, SpiderLegEnd.free), (3, SpiderLegEnd.free)],
          1 ^^^ spider_gamma n CentreStatus.none [(2, SpiderLegEnd.outward), (2, SpiderLegEnd.free), (3, SpiderLegEnd.free)],
          1 ^^^ spider_gamma n CentreStatus.none [(3, SpiderLegEnd.inward), (2, SpiderLegEnd.free), (3, SpiderLegEnd.free)],
          0 ^^^ spider_gamma n CentreStatus.none [(3, SpiderLegEnd.outward), (2, SpiderLegEnd.free), (3, SpiderLegEnd.free)],
          0 ^^^ spider_gamma n CentreStatus.none [(4, SpiderLegEnd.inward), (2, SpiderLegEnd.free), (3, SpiderLegEnd.free)],
          1 ^^^ spider_gamma n CentreStatus.incoming [(5, SpiderLegEnd.inward), (3, SpiderLegEnd.free)],
          1 ^^^ spider_gamma n CentreStatus.outgoing [(5, SpiderLegEnd.inward), (3, SpiderLegEnd.free)],
          0 ^^^ spider_gamma n CentreStatus.none [(1, SpiderLegEnd.inward), (5, SpiderLegEnd.inward), (3, SpiderLegEnd.free)],
          0 ^^^ spider_gamma n CentreStatus.none [(1, SpiderLegEnd.outward), (5, SpiderLegEnd.inward), (3, SpiderLegEnd.free)],
          2 ^^^ spider_gamma n CentreStatus.incoming [(5, SpiderLegEnd.inward), (2, SpiderLegEnd.free)],
          2 ^^^ spider_gamma n CentreStatus.outgoing [(5, SpiderLegEnd.inward), (2, SpiderLegEnd.free)],
          1 ^^^ spider_gamma n CentreStatus.none [(1, SpiderLegEnd.inward), (5, SpiderLegEnd.inward), (2, SpiderLegEnd.free)],
          1 ^^^ spider_gamma n CentreStatus.none [(1, SpiderLegEnd.outward), (5, SpiderLegEnd.inward), (2, SpiderLegEnd.free)],
          0 ^^^ spider_gamma n CentreStatus.none [(2, SpiderLegEnd.inward), (5, SpiderLegEnd.inward), (2, SpiderLegEnd.free)],
          0 ^^^ spider_gamma n CentreStatus.none [(2, SpiderLegEnd.outward), (5, SpiderLegEnd.inward), (2, SpiderLegEnd.free)] ] := by
  rw [spider_gamma.eq_def]
  dsimp only
  apply congr_arg nat_mex_list
  change List.flatMap _
      [((5, SpiderLegEnd.inward), 0), ((2, SpiderLegEnd.free), 1), ((3, SpiderLegEnd.free), 2)] = _
  rw [List.flatMap_cons, List.flatMap_cons, List.flatMap_cons, List.flatMap_nil]
  dsimp only
  have hr5 : List.range 5 = [0, 1, 2, 3, 4] := rfl
  have hr2 : List.range 2 = [0, 1] := rfl
  have hr3 : List.range 3 = [0, 1, 2] := rfl
  rw [hr5, hr2, hr3]
  simp [spider_rho, spider_update_centre]
