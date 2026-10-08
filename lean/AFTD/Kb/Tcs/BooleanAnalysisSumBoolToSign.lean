import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSign
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSignFalse
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSignTrue
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSignSq
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSignMulSelf
import AFTD.Kb.Tcs.BooleanAnalysisChiSSingleton

/-!
# BooleanAnalysis.sum_boolToSign

Topic: combinatorics   Node: 0e7ba5b01ff3

Provenance: helper lemma. TCSlib, `BooleanAnalysis.sum_boolToSign`. Lean proof by Jingzhen Sha, Allan Li, Hydroxyi, Mina, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Basic.lean (Apache-2.0); 1 verbatim; compiled here.

Sign encoding sums to zero over the Booleans. Let $\sigma\colon\mathrm{Bool}\to\{-1,1\}$ be the sign encoding, sending the value
*false* to $1$ and the value *true* to $-1$. Summing $\sigma$ over the two Boolean
values yields
\[
  \sum_{b\in\mathrm{Bool}} \sigma(b) = 0.
\]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option maxHeartbeats 400000 in
open scoped BigOperators in
variable {n : ℕ} in
/-- The sum of `boolToSign` over all bits is zero. -/
@[simp]
lemma BooleanAnalysis.sum_boolToSign : ∑ b : Bool, boolToSign b = 0 := by
  simp [boolToSign]
