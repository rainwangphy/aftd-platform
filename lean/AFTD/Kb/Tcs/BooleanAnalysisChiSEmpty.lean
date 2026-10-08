import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisChiS

/-!
# BooleanAnalysis.chiS_empty

Topic: combinatorics   Node: 2f37f5c5b688

Provenance: helper lemma. TCSlib, `BooleanAnalysis.chiS_empty`. Lean proof by Jingzhen Sha, Allan Li, Hydroxyi, Mina, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Basic.lean (Apache-2.0); 1 adapted; compiled here.

Empty-set Walsh character. The Walsh–Fourier character associated to the empty subset of $[n]$ is the constant
function equal to $1$; that is, $\chi_\emptyset(x) = 1$ for every point $x$ of the
Boolean hypercube $\{0,1\}^n$.
-/

set_option maxHeartbeats 400000 in
open scoped BigOperators in
variable {n : ℕ} in
/-- The character `χ_∅` is the constant function `1`. -/
@[simp]
lemma BooleanAnalysis.chiS_empty : (BooleanAnalysis.chiS (∅ : Finset (Fin n))) = fun _ ↦ 1 := by
  ext x; simp [chiS]
