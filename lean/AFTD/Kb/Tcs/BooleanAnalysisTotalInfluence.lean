import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisInfluence

/-!
# BooleanAnalysis.totalInfluence

Topic: combinatorics   Node: c970703220fa

Provenance: formalization of a published result. Source: TCSlib, `BooleanAnalysis.totalInfluence`. Lean proof by Jingzhen Sha, Allan Li, Hydroxyi, Mina, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Basic.lean (Apache-2.0); 1 verbatim; compiled here.

$I[f] = \sum_{i=1}^n \mathrm{Inf}_i[f]$.
-/

set_option maxHeartbeats 400000 in
open scoped BigOperators in
variable {n : ℕ} in
/-- The **total influence** of `f`: `I[f] = ∑_{i=1}^{n} Inf_i[f]`. **Source:** [OD14, §2.1]. -/
noncomputable def BooleanAnalysis.totalInfluence (f : BooleanFunc n) : ℝ :=
  ∑ i : Fin n, influence i f
