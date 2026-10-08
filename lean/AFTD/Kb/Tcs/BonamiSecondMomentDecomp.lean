import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBoolCube
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisExpect
import AFTD.Kb.Tcs.BooleanAnalysisUniformWeight
import AFTD.Kb.Tcs.BonamiAvgLast
import AFTD.Kb.Tcs.BonamiDiffLast
import AFTD.Kb.Tcs.BonamiRestrictLast
import AFTD.Kb.Tcs.BonamiRestrictLastTrueEq
import AFTD.Kb.Tcs.BonamiSumBoolCubeSucc

/-!
# Bonami.second_moment_decomp

Topic: combinatorics   Node: 6f4895d6cb1d

Provenance: helper lemma. TCSlib, `Bonami.second_moment_decomp`. Lean proof by Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Hypercontractivity/Decomposition.lean (Apache-2.0); 1 verbatim; compiled here.

Second-moment decomposition over the last coordinate. Let $f : \{0,1\}^{n+1} \to \bbr$ be a Boolean function on $n+1$ variables. Define its
average and half-difference over the last coordinate as the functions on $n$ variables
\[
g(x) = \tfrac12\bigl(f(x,0) + f(x,1)\bigr), \qquad h(x) = \tfrac12\bigl(f(x,0) -
f(x,1)\bigr).
\]
Then, with the expectation on the left taken under the uniform measure on
$\{0,1\}^{n+1}$ and those on the right under the uniform measure on $\{0,1\}^n$, the
second moment of $f$ decomposes as
\[
  \E\bigl[f^2\bigr] = \E\bigl[g^2\bigr] + \E\bigl[h^2\bigr].
\]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BooleanAnalysis in
/-- Decomposes a second moment into the average and half-difference components. **Source:** [OD14, Cor. 9.6 (proof), Eq. (9.2)]. -/
lemma Bonami.second_moment_decomp {n : ℕ} (f : BooleanFunc (n + 1)) :
    expect (fun x => f x ^ 2) =
      expect (fun x => avgLast f x ^ 2) + expect (fun x => diffLast f x ^ 2) := by
  unfold expect
  ring_nf
  have h_expand :
      ∑ x : BoolCube (n + 1), f x ^ 2 =
        ∑ x : BoolCube n, (avgLast f x + diffLast f x) ^ 2 +
        ∑ x : BoolCube n, (avgLast f x - diffLast f x) ^ 2 := by
    convert sum_boolCube_succ (fun x => f x ^ 2) using 1
    congr! 2
    · exact congr_arg (· ^ 2) (by
        unfold avgLast diffLast restrictLast
        ring)
    · simpa only [restrictLast] using
        congrArg (fun y : ℝ => y ^ 2) (restrictLast_true_eq f _).symm
  simp_all +decide [add_sq, sub_sq, Finset.sum_add_distrib, Finset.mul_sum _ _ _]
  ring_nf
  norm_num [← Finset.mul_sum _ _ _, ← Finset.sum_mul, uniformWeight]
  ring
