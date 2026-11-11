import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BalancedDraftGaussianLaw

/-!
# balanced_draft_joint_gaussian_law

Topic: fair_division   Node: e76234a9e1e7

Provenance: helper lemma. Definitions and auxiliary facts for OP-1493, the joint Gaussian limit for balanced sincere drafting.

The joint probability law of independent centered Gaussian coordinates with the proposed variance.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

noncomputable def balanced_draft_joint_gaussian_law (n : ℕ) : ProbabilityMeasure (Fin n → ℝ) :=
  ProbabilityMeasure.pi fun _ : Fin n =>
    balanced_draft_gaussian_law n
