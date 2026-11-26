import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.OnlineICDecision
import AFTD.Kb.GameTheoryEconomics.IcWinnerNat
import AFTD.Kb.GameTheoryEconomics.IcWinner

/-!
# ic_winner_zero

Topic: social_choice   Node: a076bcf9d277

Provenance: helper lemma. arXiv:2611.30683 Sec. 2.2, Stay or Switch? Metric Distortion with Online Candidate Arrivals

Under any online rule and preference profile, the winner at round 0 with proof h0 : 0 < T is candidate ⟨0, h0⟩ in Fin T.
-/

/-- At round 0, the first arriving candidate is the initial winner. -/
theorem ic_winner_zero {T : ℕ} (rule : OnlineICDecision T) {V : Type} [Fintype V]
    (prof : V → LinearOrder (Fin T)) (h0 : 0 < T) :
    ic_winner rule prof ⟨0, h0⟩ = ⟨0, h0⟩ := rfl
