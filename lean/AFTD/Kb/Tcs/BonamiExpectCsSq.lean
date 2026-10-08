import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBoolCube
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisExpect
import AFTD.Kb.Tcs.BooleanAnalysisUniformWeight

/-!
# Bonami.expect_cs_sq

Topic: combinatorics   Node: fec618d9556d

Provenance: helper lemma. TCSlib, `Bonami.expect_cs_sq`. Lean proof by Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Hypercontractivity/Decomposition.lean (Apache-2.0); 1 verbatim; compiled here.

Cauchy–Schwarz for the uniform expectation. Let $g, h : \{0,1\}^n \to \bbr$ be Boolean functions, and let $\E[\,\cdot\,]$ denote the
expectation under the uniform measure on the hypercube $\{0,1\}^n$. Then
\[
  \bigl(\E[g^2 h^2]\bigr)^2 \;\le\; \E[g^4]\cdot\E[h^4].
\]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BooleanAnalysis in
/-- Applies Cauchy--Schwarz to the square functions of two Boolean functions. **Source:** [OD14, Cor. 9.6 (proof)]. -/
lemma Bonami.expect_cs_sq {n : ℕ} (g h : BooleanFunc n) :
    expect (fun x => g x ^ 2 * h x ^ 2) ^ 2 ≤
      expect (fun x => g x ^ 4) * expect (fun x => h x ^ 4) := by
  norm_num [expect] at *
  have h_cauchy_schwarz :
      (∑ x, g x ^ 2 * h x ^ 2) ^ 2 ≤ (∑ x, g x ^ 4) * (∑ x, h x ^ 4) := by
    have h_cs : ∀ u v : BoolCube n → ℝ,
        (∑ x, u x * v x) ^ 2 ≤ (∑ x, u x ^ 2) * (∑ x, v x ^ 2) :=
      fun u v => Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u v
    convert h_cs (fun x => g x ^ 2) (fun x => h x ^ 2) using 3 <;> ring
  nlinarith [show 0 ≤ uniformWeight n ^ 2 by positivity]
