import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BalancedDraftUniformUnitLaw

/-!
# balanced_draft_input_law

Topic: fair_division   Node: 0e89bc8a2d40

Provenance: helper lemma. Definitions and auxiliary facts for OP-1493, the joint Gaussian limit for balanced sincere drafting.

The finite product probability measure in which every agent-good value is an independent uniform random variable on the unit interval.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

noncomputable def balanced_draft_input_law (n m : ℕ) : ProbabilityMeasure (Fin n → Fin m → ℝ) :=
  ProbabilityMeasure.pi fun _ : Fin n => ProbabilityMeasure.pi fun _ : Fin m => balanced_draft_uniform_unit_law
