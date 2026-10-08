import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSign

/-!
# BooleanAnalysis.dictator

Topic: combinatorics   Node: 56aadd7507ba

Provenance: formalization of a published result. Source: TCSlib, `BooleanAnalysis.dictator`. Lean proof by Jingzhen Sha, Allan Li, Hydroxyi, Mina, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Basic.lean (Apache-2.0); 1 verbatim; compiled here.

The \emph{dictator function} for coordinate $i$ outputs the sign of the $i$-th
bit: $\mathrm{dict}_i(x) = (-1)^{x_i}$.  Its unique nonzero Fourier coefficient
is $\widehat{\mathrm{dict}_i}(\{i\}) = 1$.
-/

set_option maxHeartbeats 400000 in
open scoped BigOperators in
variable {n : ℕ} in
/-- The **dictator function** for coordinate `i`: `f(x) = (-1)^{x_i}`. Its only nonzero Fourier coefficient is `f̂({i}) = 1`. -/
noncomputable def BooleanAnalysis.dictator (i : Fin n) : BooleanFunc n :=
  fun x ↦ boolToSign (x i)
