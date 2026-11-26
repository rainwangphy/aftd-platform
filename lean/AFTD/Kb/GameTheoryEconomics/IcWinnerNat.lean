import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.OnlineICDecision

/-!
# ic_winner_nat

Topic: social_choice   Node: 8e85a44d9fe5

Provenance: formalization of a published result. Source: arXiv:2611.30683 Sec. 2.2 and Sec. 3.1, Stay or Switch? Metric Distortion with Online Candidate Arrivals

Given an online rule, a finite voter type V, and an election profile prof of linear orders on Fin T, ic_winner_nat defines by recursion on t : ℕ (with proof ht : t < T) the candidate in Fin T elected at round t: at round 0 it returns candidate 0, and at round t+1 it compares the incumbent winner of round t against challenger t+1, switching to challenger t+1 if the rule evaluates to true on the pairwise preference vector.
-/

/-- The winner at round t under an online incumbent-challenger voting rule, indexed by Nat. -/
def ic_winner_nat {T : ℕ} (rule : OnlineICDecision T) {V : Type} [Fintype V]
    (prof : V → LinearOrder (Fin T)) : (t : ℕ) → (ht : t < T) → Fin T
  | 0, h0 => ⟨0, h0⟩
  | t + 1, ht =>
    let x_prev := ic_winner_nat rule prof t (Nat.lt_of_succ_lt ht)
    let pref : V → Bool := fun v =>
      letI := prof v
      decide (x_prev < ⟨t + 1, ht⟩)
    if rule V ⟨t + 1, ht⟩ pref then ⟨t + 1, ht⟩ else x_prev
