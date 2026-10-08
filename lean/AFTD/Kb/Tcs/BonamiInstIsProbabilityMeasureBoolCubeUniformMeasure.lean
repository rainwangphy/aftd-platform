import AFTD.Prelude
import AFTD.Kb.Tcs.BonamiUniformMeasure
import AFTD.Kb.Tcs.BooleanAnalysisChiSSingleton
import AFTD.Kb.Tcs.BooleanAnalysisFlipBitFlipBit

/-!
# Bonami.instIsProbabilityMeasureBoolCubeUniformMeasure

Topic: combinatorics   Node: e287c148ef4b

Provenance: formalization of a published result. Source: TCSlib, `Bonami.instIsProbabilityMeasureBoolCubeUniformMeasure`. Lean proof by Owen McGinty, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Hypercontractivity/Bonami.lean (Apache-2.0); 1 verbatim; compiled here.

Bonami.instIsProbabilityMeasureBoolCubeUniformMeasure
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BooleanAnalysis in
open MeasureTheory Set Filter ProbabilityTheory BooleanAnalysis Real in
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] in
instance Bonami.instIsProbabilityMeasureBoolCubeUniformMeasure (n : ℕ) : IsProbabilityMeasure (uniformMeasure n) := by
  unfold uniformMeasure
  infer_instance
