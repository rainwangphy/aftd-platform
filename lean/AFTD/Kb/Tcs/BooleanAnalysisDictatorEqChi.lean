import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisChiS
import AFTD.Kb.Tcs.BooleanAnalysisDictator

/-!
# BooleanAnalysis.dictator_eq_chi

Topic: combinatorics   Node: 485adba65f8c

Provenance: helper lemma. TCSlib, `BooleanAnalysis.dictator_eq_chi`. Lean proof by Jingzhen Sha, Allan Li, Hydroxyi, Mina, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Basic.lean (Apache-2.0); 1 verbatim; compiled here.

Dictator function as a singleton character. For each coordinate $i \in [n]$, the dictator function on the Boolean hypercube
$\{0,1\}^n$ coincides with the Walsh--Fourier character associated to the singleton set
$\{i\}$; that is, $\mathrm{dict}_i = \chi_{\{i\}}$ as functions $\{0,1\}^n \to \bbr$.
-/

set_option maxHeartbeats 400000 in
open scoped BigOperators in
variable {n : ℕ} in
/-- The dictator function equals the Walsh character `χ_{i}`. -/
lemma BooleanAnalysis.dictator_eq_chi (i : Fin n) : dictator i = chiS {i} := by
  ext x; simp [dictator, chiS]
