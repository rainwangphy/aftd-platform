import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CentreStatus
import AFTD.Kb.GameTheoryEconomics.SpiderLegEnd
import AFTD.Kb.GameTheoryEconomics.NatMexList
import AFTD.Kb.GameTheoryEconomics.SpiderUpdateCentre
import AFTD.Kb.GameTheoryEconomics.SpiderRho
import AFTD.Kb.GameTheoryEconomics.SpiderGamma

/-!
# spider_gamma_root_options

Topic: combinatorial_games   Node: 17355b0fa08d

Provenance: helper lemma. step towards spider_grundy_val_one_two

The option list of the root state S(1,2,z) at fuel N+1 (with z = m+1 and N ≥ 3) is the mex of 8 explicit "head" options together with the long block (List.range m).flatMap over cuts of the leg of length z.
-/

/-- Normal form of the root S(1,2,z) option list at fuel N+1. -/
theorem spider_gamma_root_options (N z m : ℕ) (hz : z = m + 1) (hN : 3 ≤ N) :
    spider_gamma (N + 1) CentreStatus.none
        [(1, SpiderLegEnd.free), (2, SpiderLegEnd.free), (z, SpiderLegEnd.free)] =
      nat_mex_list
        ([ spider_gamma N CentreStatus.incoming [(2, SpiderLegEnd.free), (z, SpiderLegEnd.free)],
           spider_gamma N CentreStatus.outgoing [(2, SpiderLegEnd.free), (z, SpiderLegEnd.free)],
           1 ^^^ spider_gamma N CentreStatus.incoming [(1, SpiderLegEnd.free), (z, SpiderLegEnd.free)],
           1 ^^^ spider_gamma N CentreStatus.outgoing [(1, SpiderLegEnd.free), (z, SpiderLegEnd.free)],
           spider_gamma N CentreStatus.none [(1, SpiderLegEnd.inward), (1, SpiderLegEnd.free), (z, SpiderLegEnd.free)],
           spider_gamma N CentreStatus.none [(1, SpiderLegEnd.outward), (1, SpiderLegEnd.free), (z, SpiderLegEnd.free)],
           m ^^^ spider_gamma N CentreStatus.incoming [(1, SpiderLegEnd.free), (2, SpiderLegEnd.free)],
           m ^^^ spider_gamma N CentreStatus.outgoing [(1, SpiderLegEnd.free), (2, SpiderLegEnd.free)]] ++
         (List.range m).flatMap (fun i =>
           [(z - (i + 2)) ^^^ spider_gamma N CentreStatus.none [(i + 1, SpiderLegEnd.inward), (1, SpiderLegEnd.free), (2, SpiderLegEnd.free)],
            (z - (i + 2)) ^^^ spider_gamma N CentreStatus.none [(i + 1, SpiderLegEnd.outward), (1, SpiderLegEnd.free), (2, SpiderLegEnd.free)]])) := by
  have _ := hN
  subst hz
  apply congr_arg nat_mex_list
  change
    List.flatMap _ [((1, SpiderLegEnd.free), 0), ((2, SpiderLegEnd.free), 1), ((m + 1, SpiderLegEnd.free), 2)] = _
  rw [List.flatMap_cons, List.flatMap_cons, List.flatMap_cons, List.flatMap_nil]
  dsimp only
  have hr1 : List.range 1 = [0] := rfl
  have hr2 : List.range 2 = [0, 1] := rfl
  rw [hr1, hr2]
  rw [List.range_succ_eq_map (n := m)]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.flatMap_map]
  simp [spider_rho, spider_update_centre]
