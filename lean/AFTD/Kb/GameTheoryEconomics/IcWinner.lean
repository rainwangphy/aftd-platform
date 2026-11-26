import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.OnlineICDecision
import AFTD.Kb.GameTheoryEconomics.IcWinnerNat

/-!
# ic_winner

Topic: social_choice   Node: d1351bc1aaba

Provenance: formalization of a published result. Source: arXiv:2611.30683 Sec. 2.2 and Sec. 3.1, Stay or Switch? Metric Distortion with Online Candidate Arrivals

For an online rule, a finite voter type V, and a preference profile prof on Fin T, ic_winner rule prof t evaluates ic_winner_nat on t.val and t.isLt to produce the winner in Fin T at round t.
-/

/-- The winner at round t in Fin T under an online incumbent-challenger voting rule. -/
def ic_winner {T : ℕ} (rule : OnlineICDecision T) {V : Type} [Fintype V]
    (prof : V → LinearOrder (Fin T)) (t : Fin T) : Fin T := ic_winner_nat rule prof t.val t.isLt
