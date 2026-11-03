import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MoveToBottom
import AFTD.Kb.GameTheoryEconomics.MarriageMarket

/-!
# woman_cutoff_tanking

Topic: matching_markets   Node: 64902194ae84

Provenance: formalization of a published result. Source: arXiv:2610.42105 Definition 3.2

In a marriage market, the profile obtained by t-cutoff tanking by woman w: woman w is moved to the bottom of the preference list of every man m that w ranks strictly below t, while women's preferences and other men's preferences remain unchanged.
-/

/-- The marriage market profile obtained by t-cutoff tanking by woman w. -/
def woman_cutoff_tanking {M W : Type*} (market : MarriageMarket M W) (w : W) (t : M) : MarriageMarket M W := open Classical in ⟨fun m => if market.pref_w w t m then move_to_bottom (market.pref_m m) w else market.pref_m m, market.pref_w⟩
