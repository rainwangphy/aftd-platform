import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBoolCube

/-!
# Bonami.uniformMeasure

Topic: combinatorics   Node: 0401a7eb6f11

Provenance: formalization of a published result. Source: TCSlib, `Bonami.uniformMeasure`. Lean proof by Owen McGinty, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Hypercontractivity/Bonami.lean (Apache-2.0); 1 verbatim; compiled here.

The canonical uniform probability measure on the Boolean hypercube $\{0,1\}^n$.
-/

open BooleanAnalysis in
open MeasureTheory Set Filter ProbabilityTheory BooleanAnalysis Real in
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] in
/-- The canonical uniform probability measure on the Boolean Hypercube. **Source:** [OD14, Cor. 9.6 (uniform product-space specialization)]. -/
noncomputable def Bonami.uniformMeasure (n : ℕ) : Measure (BoolCube n) :=
  (PMF.uniformOfFintype (BoolCube n)).toMeasure
