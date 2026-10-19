import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiderGamma
import AFTD.Kb.GameTheoryEconomics.SpiderRho
import AFTD.Kb.GameTheoryEconomics.CentreStatus
import AFTD.Kb.GameTheoryEconomics.SpiderLegEnd

/-!
# spider_none_one_inward_one_outward_raw_opts

Topic: combinatorial_games   Node: b56442b62d1c

Provenance: helper lemma. step towards spider_blocked_none_one_inward_one_outward

The raw option list of the state (none;{(1,inward),(1,outward),(r,φ)}) after one unfolding step, in the exact order the recursion enumerates: the j = 1 cut of each of the two short legs, the j = 1 cuts of the long leg, the cuts j = 2..r-1 of the long leg (reindexed i = j-2), and the last cut j = r of the long leg, each entry being a rho coefficient xor the value of the resulting sub-state at fuel r+2.
-/

/-- The definitionally unfolded option list of the κ₁ state, still containing the sub-state values. -/
def spider_none_one_inward_one_outward_raw_opts (r : ℕ) (φ : SpiderLegEnd) : List ℕ := [ spider_gamma (r + 2) CentreStatus.incoming [(1, SpiderLegEnd.outward), (r, φ)],
      spider_gamma (r + 2) CentreStatus.outgoing [(1, SpiderLegEnd.inward), (r, φ)],
      spider_rho (r - 1) SpiderLegEnd.inward φ ^^^
        spider_gamma (r + 2) CentreStatus.incoming [(1, SpiderLegEnd.inward), (1, SpiderLegEnd.outward)],
      spider_rho (r - 1) SpiderLegEnd.outward φ ^^^
        spider_gamma (r + 2) CentreStatus.outgoing [(1, SpiderLegEnd.inward), (1, SpiderLegEnd.outward)]] ++
    (List.range (r - 2)).flatMap (fun i =>
      [ spider_rho (r - 2 - i) SpiderLegEnd.inward φ ^^^
          spider_gamma (r + 2) CentreStatus.none
            [(1, SpiderLegEnd.inward), (1, SpiderLegEnd.outward), (i + 1, SpiderLegEnd.inward)],
        spider_rho (r - 2 - i) SpiderLegEnd.outward φ ^^^
          spider_gamma (r + 2) CentreStatus.none
            [(1, SpiderLegEnd.inward), (1, SpiderLegEnd.outward), (i + 1, SpiderLegEnd.outward)]]) ++
    [ spider_rho 0 φ φ ^^^
        spider_gamma (r + 2) CentreStatus.none
          [(1, SpiderLegEnd.inward), (1, SpiderLegEnd.outward), (r - 1, φ)]]
