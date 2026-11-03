import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MoveToBottom
import AFTD.Kb.GameTheoryEconomics.MarriageMarket

/-!
# man_cutoff_tanking

Topic: matching_markets   Node: 1f033cc4a289

Provenance: formalization of a published result. Source: arXiv:2610.42105 Definition 3.2

In a marriage market, the profile obtained by t-cutoff tanking by man m: man m is moved to the bottom of the preference list of every woman w that m ranks strictly below t, while men's preferences and other women's preferences remain unchanged.
-/

/-- The marriage market profile obtained by t-cutoff tanking by man m. -/
def man_cutoff_tanking {M W : Type*} (market : MarriageMarket M W) (m : M) (t : W) : MarriageMarket M W := open Classical in ⟨market.pref_m, fun w => if market.pref_m m t w then move_to_bottom (market.pref_w w) m else market.pref_w w⟩
