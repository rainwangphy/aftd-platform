import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBoolCube
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSign
import AFTD.Kb.Tcs.BooleanAnalysisChiS
import AFTD.Kb.Tcs.BooleanAnalysisChiSMulChiS
import AFTD.Kb.Tcs.BooleanAnalysisChiSSingleton

/-!
# DecisionTree.chiS_symmDiff_singleton

Topic: circuits   Node: 0d60b2c9f265

Provenance: helper lemma. TCSlib, `DecisionTree.chiS_symmDiff_singleton`. Lean proof by Hydroxyi, Owen McGinty, Seyoon Ragavan (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/LMN/DecisionTreeFourier.lean (Apache-2.0); 1 verbatim; compiled here.

Symmetric difference by a singleton toggles a Walsh character. Let $S\subseteq[n]$, let $i\in[n]$, and let $x\in\{0,1\}^n$. Then the Walsh--Fourier
character indexed by the symmetric difference $S\mathbin{\triangle}\{i\}$ satisfies
\[
  \chi_{S\,\triangle\,\{i\}}(x) \;=\; \chi_S(x)\,\sigma(x_i),
\]
where $\sigma$ is the sign encoding $\sigma(x_i)=(-1)^{x_i}$.
-/

open BooleanAnalysis in
variable {n : ℕ} in
lemma DecisionTree.chiS_symmDiff_singleton (S : Finset (Fin n)) (i : Fin n) (x : BoolCube n) :
    chiS (symmDiff S {i}) x = chiS S x * boolToSign (x i) := by
  rw [← chiS_mul_chiS, chiS_singleton]
