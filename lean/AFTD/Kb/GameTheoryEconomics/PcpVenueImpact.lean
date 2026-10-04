import AFTD.Prelude

/-!
# pcp_venue_impact

Topic: equilibria   Node: fd27754ee2b6

Venue impact (eq. (2)): the impact of venue j is the average type of the researchers publishing there, weighted by type densities and publication counts.
-/

open Finset in
/-- The impact of venue `j` under the action profile `a` (eq. (2) of Wang–Wu–Xu): the average type of the researchers publishing there, weighted by their publication counts and type densities `μ`. -/
noncomputable def pcp_venue_impact {n k : ℕ} (θ μ : Fin n → ℝ) (a : Fin n → Fin k → ℝ) (j : Fin k) : ℝ :=
  (∑ i, a i j * μ i * θ i) / ∑ i, a i j * μ i
