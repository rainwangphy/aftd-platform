import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiderBlockedRawOpts
import AFTD.Kb.GameTheoryEconomics.SpiderBlockedLeg0Opts
import AFTD.Kb.GameTheoryEconomics.SpiderBlockedFreeLegOpts
import AFTD.Kb.GameTheoryEconomics.CentreStatus
import AFTD.Kb.GameTheoryEconomics.SpiderGamma
import AFTD.Kb.GameTheoryEconomics.SpiderLegEnd
import AFTD.Kb.GameTheoryEconomics.SpiderRho
import AFTD.Kb.GameTheoryEconomics.SpiderUpdateCentre
import AFTD.Kb.GameTheoryEconomics.SpiderBlockedOptionvalsLe

/-!
# spider_blocked_raw_opts_split

Topic: combinatorial_games   Node: 250446c145b8

Provenance: helper lemma. step towards op211_three_legged_spider_eventual_parity

The raw option list of (in;{(r,β),(1,free)}) decomposes as spider_blocked_leg0_opts r β ++ spider_blocked_free_leg_opts r β: the zipIdx over the two legs splits into the leg (r,β) (whose rest is [(1,free)]) and the leg (1,free) (whose rest is [(r,β)]), and in that order.
-/

/-- The raw option list splits as the blocked leg's options followed by the free leg's options. -/
theorem spider_blocked_raw_opts_split (r : ℕ) (beta : SpiderLegEnd) :
    spider_blocked_raw_opts r beta
      = spider_blocked_leg0_opts r beta ++ spider_blocked_free_leg_opts r beta := by first | exact spider_blocked_optionvals_le | (apply spider_blocked_optionvals_le <;> assumption) | (apply spider_blocked_optionvals_le <;> simp_all) | simpa using spider_blocked_optionvals_le | (simp only [SpiderLegEnd, spider_blocked_raw_opts, spider_blocked_leg0_opts, spider_blocked_free_leg_opts] at *; first | exact spider_blocked_optionvals_le | (apply spider_blocked_optionvals_le <;> assumption) | (apply spider_blocked_optionvals_le <;> simp_all) | simpa using spider_blocked_optionvals_le)
