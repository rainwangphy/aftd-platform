import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisInstAddCommGroupBooleanFunc

/-!
# BooleanAnalysis.instModuleRealBooleanFunc

Topic: combinatorics   Node: 64e642233bb2

Provenance: formalization of a published result. Source: TCSlib, `BooleanAnalysis.instModuleRealBooleanFunc`. Lean proof by Jingzhen Sha, Allan Li, Hydroxyi, Mina, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Basic.lean (Apache-2.0); 1 verbatim; compiled here.

BooleanAnalysis.instModuleRealBooleanFunc
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option maxHeartbeats 400000 in
open scoped BigOperators in
variable {n : ℕ} in
noncomputable instance BooleanAnalysis.instModuleRealBooleanFunc : Module ℝ (BooleanFunc n) := Pi.module _ _ _
