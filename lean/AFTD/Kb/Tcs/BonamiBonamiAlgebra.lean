import AFTD.Prelude

/-!
# Bonami.bonami_algebra

Topic: combinatorics   Node: efc353128dc4

Provenance: helper lemma. TCSlib, `Bonami.bonami_algebra`. Lean proof by Owen McGinty, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Hypercontractivity/Bonami.lean (Apache-2.0); 1 verbatim; compiled here.

Algebraic inductive step for the Bonami lemma. Fix a natural number $m$, and let $a, b, B, C$ be nonnegative real numbers and $A$ a
real number satisfying $A \le 9^{m+1} a^2$, $B \le 9^m b^2$, and $C^2 \le A B$. Then
\[
A + 6C + B \le 9^{m+1}\,(a+b)^2.
\]
-/

open MeasureTheory Set Filter ProbabilityTheory Real in
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] in
/-- Closes the algebraic recurrence in the inductive proof of the Bonami bound. **Source:** [OD14, Cor. 9.6 (proof)]. -/
lemma Bonami.bonami_algebra {m : ℕ} {a b A B C : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hA_bound : A ≤ 9 ^ (m + 1) * a ^ 2)
    (hB_bound : B ≤ 9 ^ m * b ^ 2)
    (hC_bound : C ^ 2 ≤ A * B) :
    A + 6 * C + B ≤ 9 ^ (m + 1) * (a + b) ^ 2 := by
  -- By combining terms, we can factor out common factors and simplify the expression.
  ring_nf at *;
  nlinarith [ show 0 ≤ 9 ^ m by positivity, show 0 ≤ a * b * 9 ^ m by positivity, sq_nonneg ( C - a * b * 9 ^ m * 3 ), mul_le_mul_of_nonneg_left hB_bound ( show 0 ≤ 9 ^ m by positivity ) ]
