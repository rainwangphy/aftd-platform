import AFTD.Prelude

/-!
# OnlineICDecision

Topic: social_choice   Node: 3b77a0510c3d

Provenance: formalization of a published result. Source: arXiv:2611.30683 Sec. 2.2 and Sec. 3.1, Stay or Switch? Metric Distortion with Online Candidate Arrivals

For a horizon T, OnlineICDecision T is the type of online decision rules that universally quantify over all finite types V of voters, taking each round t in Fin T and each pairwise preference vector in V -> Bool to a Bool (false to stay with the incumbent, true to switch to the challenger).
-/

/-- Decision functions for deterministic online voting rules in the partial information incumbent-challenger model. -/
def OnlineICDecision (T : ℕ) := ∀ (V : Type) [Fintype V], (t : Fin T) → (V → Bool) → Bool
