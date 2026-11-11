import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BalancedDraftAsymptoticVariance

/-!
# balanced_draft_gaussian_law

Topic: fair_division   Node: af8ccf0f3f7d

Provenance: helper lemma. Definitions and auxiliary facts for OP-1493, the joint Gaussian limit for balanced sincere drafting.

The centered Gaussian probability law whose variance is the nonnegative part of the proposed asymptotic variance; for at least two agents this is the proposed variance.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

noncomputable def balanced_draft_gaussian_law (n : ℕ) : ProbabilityMeasure ℝ :=
  ⟨gaussianReal 0 (Real.toNNReal (balanced_draft_asymptotic_variance n)), inferInstance⟩
