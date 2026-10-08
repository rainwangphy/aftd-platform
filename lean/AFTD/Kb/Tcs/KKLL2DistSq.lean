import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisExpect

/-!
# KKL.l2DistSq

Topic: combinatorics   Node: de817524b1b0

Provenance: formalization of a published result. Source: TCSlib, `KKL.l2DistSq`. Lean proof by Mina, Owen McGinty, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/KKL.lean (Apache-2.0); 1 verbatim; compiled here.

The squared $L^2$ distance between two Boolean functions is
$\E\big[(f(x) - g(x))^2\big]$ under the uniform measure on the cube.
-/

set_option maxHeartbeats 800000 in
open scoped BigOperators in
open BooleanAnalysis in
variable {n : ℕ} in
open Classical in
/-- Defines the squared `L²` distance between two Boolean functions. **Source:** [OD14, Ch. 10]. -/
noncomputable def KKL.l2DistSq (f g : BooleanFunc n) : ℝ :=
  expect (fun x => (f x - g x) ^ 2)
