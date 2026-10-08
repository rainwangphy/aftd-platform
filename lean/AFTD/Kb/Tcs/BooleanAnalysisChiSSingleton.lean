import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBoolCube
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSign
import AFTD.Kb.Tcs.BooleanAnalysisChiS

/-!
# BooleanAnalysis.chiS_singleton

Topic: combinatorics   Node: 61f7946a08c6

Provenance: helper lemma. TCSlib, `BooleanAnalysis.chiS_singleton`. Lean proof by Jingzhen Sha, Allan Li, Hydroxyi, Mina, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Basic.lean (Apache-2.0); 1 adapted; compiled here.

Value of a singleton Walsh character. Fix a dimension $n$, a coordinate $i \in [n]$, and a point $x$ of the Boolean hypercube
$\{0,1\}^n$. Then the Walsh--Fourier character of the singleton set $\{i\}$, evaluated
at $x$, is the sign encoding of the $i$-th coordinate of $x$:
\[
  \chi_{\{i\}}(x) \;=\; \sigma(x_i).
\]
-/

set_option maxHeartbeats 400000 in
open scoped BigOperators in
variable {n : ℕ} in
/-- The character `χ_{i}` for a singleton `{i}` equals `(-1)^{x_i}`. -/
@[simp]
lemma BooleanAnalysis.chiS_singleton (i : Fin n) (x : BoolCube n) :
    (BooleanAnalysis.chiS {i}) x = boolToSign (x i) := by
  simp [chiS]
