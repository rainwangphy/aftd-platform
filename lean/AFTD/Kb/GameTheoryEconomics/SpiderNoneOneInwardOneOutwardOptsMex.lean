import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiderNoneOneInwardOneOutwardOptsNotMem
import AFTD.Kb.GameTheoryEconomics.SpiderNoneOneInwardOneOutwardOptsAllLtMem
import AFTD.Kb.GameTheoryEconomics.NatMexListNotMemAndLt
import AFTD.Kb.GameTheoryEconomics.SpiderMexListEqOfNotMemAndLtMem
import AFTD.Kb.GameTheoryEconomics.SpiderLegEnd
import AFTD.Kb.GameTheoryEconomics.SpiderNoneOneInwardOneOutwardOpts
import AFTD.Kb.GameTheoryEconomics.NatMexList

/-!
# spider_none_one_inward_one_outward_opts_mex

Topic: combinatorial_games   Node: 02860a47928c

Provenance: helper lemma. step towards spider_blocked_none_one_inward_one_outward

For r ≥ 2 and φ ≠ free, the mex of the explicit option list of the κ₁ configuration equals r.
-/

/-- The mex of the closed-form option list of the κ₁ family equals r. -/
theorem spider_none_one_inward_one_outward_opts_mex (r : ℕ) (hr : 2 ≤ r) (φ : SpiderLegEnd) (hφ : φ ≠ SpiderLegEnd.free) :
    nat_mex_list (spider_none_one_inward_one_outward_opts r φ) = r := spider_mex_list_eq_of_not_mem_and_lt_mem _ _
    (spider_none_one_inward_one_outward_opts_not_mem r hr φ hφ)
    (spider_none_one_inward_one_outward_opts_all_lt_mem r hr φ hφ)
