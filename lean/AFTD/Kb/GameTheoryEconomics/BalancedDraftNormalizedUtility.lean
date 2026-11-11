import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BalancedDraftValueOrder
import AFTD.Kb.GameTheoryEconomics.DraftRule

/-!
# balanced_draft_normalized_utility

Topic: fair_division   Node: 708b430f5822

Provenance: helper lemma. Definitions and auxiliary facts for OP-1493, the joint Gaussian limit for balanced sincere drafting.

For a schedule and a real valuation profile, multiply an agent's sincere-draft bundle value by the number of agents and divide by her total value; ties favor the larger good index and division by zero is zero.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

noncomputable def balanced_draft_normalized_utility (n m : ℕ) (schedule : Fin m → Fin n)
    (v : Fin n → Fin m → ℝ) (i : Fin n) : ℝ := by
  classical
  exact (n : ℝ) * (∑ g ∈ draft_rule schedule (fun j => balanced_draft_value_order (v j)) i, v i g) /
    (∑ g : Fin m, v i g)
