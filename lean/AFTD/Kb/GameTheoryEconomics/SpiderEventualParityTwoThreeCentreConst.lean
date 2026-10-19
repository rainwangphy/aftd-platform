import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiderLegEnd
import AFTD.Kb.GameTheoryEconomics.CentreStatus
import AFTD.Kb.GameTheoryEconomics.SpiderGamma

/-!
# spider_eventual_parity_two_three_centre_const

Topic: combinatorial_games   Node: 564184d42bdc

Provenance: helper lemma. step towards spider_eventual_parity_two_three

The paper's constant W_in(κ0) = Γ(in;{2^*,3^*}) and W_out(κ0) = Γ(out;{2^*,3^*}) for the configuration κ0 = (n;{2^*,3^*}) both equal 3.
-/

/-- The two two-leg constant positions (i;{2^*,3^*}) and (o;{2^*,3^*}) both have Grundy value 3. -/
theorem spider_eventual_parity_two_three_centre_const :
    spider_gamma 6 CentreStatus.incoming [(2, SpiderLegEnd.free), (3, SpiderLegEnd.free)] = 3 ∧
    spider_gamma 6 CentreStatus.outgoing [(2, SpiderLegEnd.free), (3, SpiderLegEnd.free)] = 3 := by
  decide
