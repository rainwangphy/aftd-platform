import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiderNoneOneInwardOneOutwardRawOpts
import AFTD.Kb.GameTheoryEconomics.SpiderNoneOneInwardOneOutwardOpts
import AFTD.Kb.GameTheoryEconomics.SpiderBlockedIncomingOneOutward
import AFTD.Kb.GameTheoryEconomics.SpiderBlockedOutgoingOneInward
import AFTD.Kb.GameTheoryEconomics.SpiderTwoLegShortShortZero
import AFTD.Kb.GameTheoryEconomics.SpiderRhoZeroSame
import AFTD.Kb.GameTheoryEconomics.SpiderGammaRotateThreeShortLegs
import AFTD.Kb.GameTheoryEconomics.SpiderGammaFuelIndependent
import AFTD.Kb.GameTheoryEconomics.SpiderLegEnd
import AFTD.Kb.GameTheoryEconomics.NatMexList
import AFTD.Kb.GameTheoryEconomics.SpiderGamma
import AFTD.Kb.GameTheoryEconomics.SpiderRho
import AFTD.Kb.GameTheoryEconomics.CentreStatus

/-!
# spider_blocked_none_one_inward_one_outward_opts_eq

Topic: combinatorial_games   Node: 4c6bc01c5158

Provenance: helper lemma. step towards spider_blocked_none_one_inward_one_outward

For r ≥ 2, φ ≠ free, and assuming the closed form for all smaller levels, the mex of the raw option list equals the mex of the explicit closed-form list spider_none_one_inward_one_outward_opts r φ.
-/

/-- Substituting all sub-state values in the raw option list yields the closed-form option list. -/
theorem spider_blocked_none_one_inward_one_outward_opts_eq (r : ℕ) (hr : 2 ≤ r) (φ : SpiderLegEnd) (hφ : φ ≠ SpiderLegEnd.free)
    (ih : ∀ r' < r, 1 ≤ r' → ∀ φ' : SpiderLegEnd, φ' ≠ SpiderLegEnd.free →
      spider_gamma (r' + 3) CentreStatus.none
        [(1, SpiderLegEnd.inward), (1, SpiderLegEnd.outward), (r', φ')] = r') :
    nat_mex_list (spider_none_one_inward_one_outward_raw_opts r φ) =
      nat_mex_list (spider_none_one_inward_one_outward_opts r φ) := by
  have h1 : spider_gamma (r + 2) CentreStatus.incoming [(1, SpiderLegEnd.outward), (r, φ)] = r ^^^ 1 :=
    spider_blocked_incoming_one_outward r (by omega) φ hφ
  have h2 : spider_gamma (r + 2) CentreStatus.outgoing [(1, SpiderLegEnd.inward), (r, φ)] = r ^^^ 1 :=
    spider_blocked_outgoing_one_inward r (by omega) φ hφ
  have hshort := spider_two_leg_short_short_zero (r + 2) (by omega)
  have h3 : spider_rho (r - 1) SpiderLegEnd.inward φ ^^^
        spider_gamma (r + 2) CentreStatus.incoming [(1, SpiderLegEnd.inward), (1, SpiderLegEnd.outward)]
      = spider_rho (r - 1) SpiderLegEnd.inward φ := by rw [hshort.1, Nat.xor_zero]
  have h4 : spider_rho (r - 1) SpiderLegEnd.outward φ ^^^
        spider_gamma (r + 2) CentreStatus.outgoing [(1, SpiderLegEnd.inward), (1, SpiderLegEnd.outward)]
      = spider_rho (r - 1) SpiderLegEnd.outward φ := by rw [hshort.2, Nat.xor_zero]
  have hhead : [spider_gamma (r + 2) CentreStatus.incoming [(1, SpiderLegEnd.outward), (r, φ)],
        spider_gamma (r + 2) CentreStatus.outgoing [(1, SpiderLegEnd.inward), (r, φ)],
        spider_rho (r - 1) SpiderLegEnd.inward φ ^^^
          spider_gamma (r + 2) CentreStatus.incoming [(1, SpiderLegEnd.inward), (1, SpiderLegEnd.outward)],
        spider_rho (r - 1) SpiderLegEnd.outward φ ^^^
          spider_gamma (r + 2) CentreStatus.outgoing [(1, SpiderLegEnd.inward), (1, SpiderLegEnd.outward)]] =
      [r ^^^ 1, r ^^^ 1, spider_rho (r - 1) SpiderLegEnd.inward φ, spider_rho (r - 1) SpiderLegEnd.outward φ] := by
    simp only [h1, h2, h3, h4]
  have hmid : List.flatMap
        (fun i =>
          [spider_rho (r - 2 - i) SpiderLegEnd.inward φ ^^^
              spider_gamma (r + 2) CentreStatus.none
                [(1, SpiderLegEnd.inward), (1, SpiderLegEnd.outward), (i + 1, SpiderLegEnd.inward)],
            spider_rho (r - 2 - i) SpiderLegEnd.outward φ ^^^
              spider_gamma (r + 2) CentreStatus.none
                [(1, SpiderLegEnd.inward), (1, SpiderLegEnd.outward), (i + 1, SpiderLegEnd.outward)]])
        (List.range (r - 2)) =
      List.flatMap
        (fun i =>
          [spider_rho (r - 2 - i) SpiderLegEnd.inward φ ^^^ i + 1,
            spider_rho (r - 2 - i) SpiderLegEnd.outward φ ^^^ i + 1])
        (List.range (r - 2)) := by
    apply List.flatMap_congr
    intro i hi
    simp only [List.mem_range] at hi
    have hin : spider_gamma (r + 2) CentreStatus.none
        [(1, SpiderLegEnd.inward), (1, SpiderLegEnd.outward), (i + 1, SpiderLegEnd.inward)] = i + 1 := by
      rw [spider_gamma_fuel_independent (r + 2) CentreStatus.none _ (by simp; omega)]
      rw [show (([(1, SpiderLegEnd.inward), (1, SpiderLegEnd.outward), (i + 1, SpiderLegEnd.inward)].map Prod.fst).sum + 1) = (i+1)+3 from by simp; omega]
      exact ih (i + 1) (by omega) (by omega) _ (by simp)
    have hout : spider_gamma (r + 2) CentreStatus.none
        [(1, SpiderLegEnd.inward), (1, SpiderLegEnd.outward), (i + 1, SpiderLegEnd.outward)] = i + 1 := by
      rw [spider_gamma_fuel_independent (r + 2) CentreStatus.none _ (by simp; omega)]
      rw [show (([(1, SpiderLegEnd.inward), (1, SpiderLegEnd.outward), (i + 1, SpiderLegEnd.outward)].map Prod.fst).sum + 1) = (i+1)+3 from by simp; omega]
      exact ih (i + 1) (by omega) (by omega) _ (by simp)
    simp only [hin, hout]
  have htail : [spider_rho 0 φ φ ^^^
        spider_gamma (r + 2) CentreStatus.none [(1, SpiderLegEnd.inward), (1, SpiderLegEnd.outward), (r - 1, φ)]] =
      [r - 1] := by
    simp only [spider_rho_zero_same φ hφ, Nat.zero_xor]
    rw [show r + 2 = (r - 1) + 3 from by omega]
    rw [ih (r - 1) (by omega) (by omega) φ hφ]
  apply congr_arg nat_mex_list
  simp only [spider_none_one_inward_one_outward_raw_opts, spider_none_one_inward_one_outward_opts]
  rw [hhead, hmid, htail]
