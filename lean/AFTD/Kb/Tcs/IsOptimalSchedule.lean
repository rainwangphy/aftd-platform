import AFTD.Prelude
import AFTD.Kb.Tcs.RentOrBuyCost

/-!
# is_optimal_schedule

Topic: online_algorithms   Node: f834b46f5512

Provenance: formalization of a published result. Source: arXiv:2611.06955, Definition 3

A schedule r_star : Fin T → Bool is optimal with hindsight for increments a : Fin (T - 1) → NNReal and reset price K : ℝ if for every schedule r : Fin T → Bool, rent_or_buy_cost T a K r_star ≤ rent_or_buy_cost T a K r.
-/

/-- A schedule r_star is optimal with hindsight for a session if its total cost is at most that of any schedule. -/
def is_optimal_schedule (T : ℕ) (a : Fin (T - 1) → NNReal) (K : ℝ) (r_star : Fin T → Bool) : Prop := ∀ r : Fin T → Bool, rent_or_buy_cost T a K r_star ≤ rent_or_buy_cost T a K r
