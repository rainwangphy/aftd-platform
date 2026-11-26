import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.OnlineICDecision
import AFTD.Kb.GameTheoryEconomics.IcWinnerNat
import AFTD.Kb.GameTheoryEconomics.IcWinner
import AFTD.Kb.GameTheoryEconomics.CandidateMetricSocialCost
import AFTD.Kb.GameTheoryEconomics.IsConsistentPseudometric

/-!
# is_online_distortion_bounded

Topic: social_choice   Node: 3f80dd30aa7a

Provenance: formalization of a published result. Source: arXiv:2611.30683 Sec. 2.2, Stay or Switch? Metric Distortion with Online Candidate Arrivals

A rule achieves metric distortion at most D for horizon T if for every nonempty finite voter type V, every pseudometric space on V ⊕ Fin T, every preference profile prof consistent with the pseudometric, every round t in Fin T, and every candidate y ≤ t in Fin T, the social cost of the round-t winner is at most D times the social cost of y.
-/

/-- An online voting rule achieves metric distortion at most D if at every round t, the winner's social cost is at most D times that of any candidate arriving by round t. -/
def is_online_distortion_bounded {T : ℕ} (rule : OnlineICDecision T) (D : ℝ) : Prop := ∀ (V : Type) [Fintype V] [Nonempty V]
    [PseudoMetricSpace (V ⊕ Fin T)]
    (prof : V → LinearOrder (Fin T))
    (_h_metric : is_consistent_pseudometric V (Fin T) prof)
    (t : Fin T) (y : Fin T) (_hy : y ≤ t),
    candidate_metric_social_cost V (ic_winner rule prof t) ≤
      D * candidate_metric_social_cost V y
