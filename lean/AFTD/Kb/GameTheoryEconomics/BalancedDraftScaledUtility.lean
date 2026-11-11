import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BalancedDraftNormalizedUtility

/-!
# balanced_draft_scaled_utility

Topic: fair_division   Node: 4c1f6be1466b

Provenance: helper lemma. Definitions and auxiliary facts for OP-1493, the joint Gaussian limit for balanced sincere drafting.

The vector of normalized sincere-draft utilities, each centered at 2n/(n+1) and multiplied by the square root of the number of goods.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

noncomputable def balanced_draft_scaled_utility (n m : ℕ) (schedule : Fin m → Fin n)
    (v : Fin n → Fin m → ℝ) : Fin n → ℝ := by
  classical
  exact fun i => Real.sqrt m *
    (balanced_draft_normalized_utility n m schedule v i - 2 * (n : ℝ) / ((n : ℝ) + 1))
