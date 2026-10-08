import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisExpect
import AFTD.Kb.Tcs.BonamiRestrictLast
import AFTD.Kb.Tcs.BonamiSumBoolCubeSucc
import AFTD.Kb.Tcs.BonamiUniformWeightSucc

/-!
# Bonami.expect_succ_eq

Topic: combinatorics   Node: 5f9bee7698b1

Provenance: helper lemma. TCSlib, `Bonami.expect_succ_eq`. Lean proof by Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Hypercontractivity/Decomposition.lean (Apache-2.0); 1 verbatim; compiled here.

Expectation splits over the last coordinate. Let $\varphi : \{0,1\}^{n+1} \to \bbr$ be a Boolean function on $n+1$ variables, and for
a bit $b \in \{0,1\}$ let $\varphi_b : \{0,1\}^n \to \bbr$, $\varphi_b(x) = \varphi(x,
b)$, be its restriction obtained by fixing the last coordinate to $b$. Then the
expectation of $\varphi$ under the uniform measure on $\{0,1\}^{n+1}$ is the average of
the expectations of its two restrictions:
\[
  \E[\varphi] \;=\; \frac{\E[\varphi_{0}] + \E[\varphi_{1}]}{2}.
\]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BooleanAnalysis in
/-- Expresses expectation on an `(n + 1)`-cube as the average over the two restrictions. **Source:** [OD14, Cor. 9.6 (proof)]. -/
lemma Bonami.expect_succ_eq {n : ℕ} (φ : BooleanFunc (n + 1)) :
    expect φ = (expect (restrictLast φ false) + expect (restrictLast φ true)) / 2 := by
  unfold expect restrictLast
  rw [sum_boolCube_succ, uniformWeight_succ]
  ring
