import AFTD.Prelude
import AFTD.Kb.Tcs.DeadlineRequest

/-!
# instanceHorizon

Topic: online_algorithms   Node: 8abb6d67d086

Provenance: formalization of a published result. Source: arXiv:2610.18767 Sec. 2

The finite time horizon of a list of deadline requests, defined as one more than the maximum deadline, or zero if empty.
-/

/-- The time horizon of a list of deadline requests. -/
def instanceHorizon {α : Type*} (reqs : List (DeadlineRequest α)) : ℕ := reqs.foldr (fun r m => max (r.deadline + 1) m) 0
