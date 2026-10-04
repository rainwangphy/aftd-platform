import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PcxCost
import AFTD.Kb.GameTheoryEconomics.PcxImpact

/-!
# pcx_action

Topic: equilibria   Node: 0a39f7772e22

The closed-form best-response action profile of the binary instance against the venue impacts pcx_impact x.
-/

open Finset in
/-- Best-response action profile of the instance against the venue impacts `pcx_impact x` (closed form of Lemma 3.1 with `α = 1/2`, `β = 2`). -/
noncomputable def pcx_action (x : ℝ) : Fin 2 → Fin 2 → ℝ := fun i j =>
  pcx_impact x j ^ 4 / (pcx_cost i j ^ 2 * ∑ l, pcx_impact x l ^ 4 / pcx_cost i l)
