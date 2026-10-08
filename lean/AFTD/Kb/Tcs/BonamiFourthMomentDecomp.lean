import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisExpect
import AFTD.Kb.Tcs.BonamiAvgLast
import AFTD.Kb.Tcs.BonamiDiffLast
import AFTD.Kb.Tcs.BonamiExpectSuccEq
import AFTD.Kb.Tcs.BonamiRestrictLast

/-!
# Bonami.fourth_moment_decomp

Topic: combinatorics   Node: dfb77ef2ec63

Provenance: helper lemma. TCSlib, `Bonami.fourth_moment_decomp`. Lean proof by Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Hypercontractivity/Decomposition.lean (Apache-2.0); 1 verbatim; compiled here.

Fourth-moment decomposition over the last coordinate. Let $f : \{0,1\}^{n+1} \to \bbr$ be a Boolean function on $n+1$ variables, and let $g$
and $h$ be the average and the half-difference of $f$ over its last coordinate, so that
$g(x) = \tfrac12\bigl(f(x,0) + f(x,1)\bigr)$ and $h(x) = \tfrac12\bigl(f(x,0) -
f(x,1)\bigr)$ for $x \in \{0,1\}^n$. Then, with all expectations taken under the uniform
measure, the fourth moment of $f$ decomposes as
\[
\E[f^4] \;=\; \E[g^4] + 6\,\E[g^2 h^2] + \E[h^4].
\]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BooleanAnalysis in
/-- Decomposes a fourth moment into the average and half-difference components. **Source:** [OD14, Cor. 9.6 (proof), Eq. (9.1)]. -/
lemma Bonami.fourth_moment_decomp {n : ℕ} (f : BooleanFunc (n + 1)) :
    expect (fun x => f x ^ 4) =
    expect (fun x => avgLast f x ^ 4) +
      6 * expect (fun x => avgLast f x ^ 2 * diffLast f x ^ 2) +
      expect (fun x => diffLast f x ^ 4) := by
  have h_decomp :
      expect (fun x => f x ^ 4) =
        expect (fun x => (avgLast f x + diffLast f x) ^ 4) / 2 +
        expect (fun x => (avgLast f x - diffLast f x) ^ 4) / 2 := by
    convert expect_succ_eq (fun x => f x ^ 4) using 1
    unfold expect restrictLast avgLast diffLast
    ring_nf
    rfl
  rw [h_decomp]
  ring_nf
  norm_num [Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul]
  ring_nf
  unfold expect
  norm_num [Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul]
  ring_nf
  simpa only [mul_assoc, ← Finset.mul_sum _ _ _, ← Finset.sum_mul] using by ring
