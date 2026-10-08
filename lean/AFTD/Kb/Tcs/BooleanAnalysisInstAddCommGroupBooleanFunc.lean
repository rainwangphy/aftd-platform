import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc

/-!
# BooleanAnalysis.instAddCommGroupBooleanFunc

Topic: combinatorics   Node: f19c0454fa37

Provenance: formalization of a published result. Source: TCSlib, `BooleanAnalysis.instAddCommGroupBooleanFunc`. Lean proof by Jingzhen Sha, Allan Li, Hydroxyi, Mina, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Basic.lean (Apache-2.0); 1 verbatim; compiled here.

Boolean functions form an `ℝ`-vector space.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option maxHeartbeats 400000 in
open scoped BigOperators in
variable {n : ℕ} in
/-- Boolean functions form an `ℝ`-vector space. -/
instance BooleanAnalysis.instAddCommGroupBooleanFunc : AddCommGroup (BooleanFunc n) := Pi.addCommGroup
