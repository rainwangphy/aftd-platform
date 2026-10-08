import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBoolCube
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSign
import AFTD.Kb.Tcs.BooleanAnalysisChiS
import AFTD.Kb.Tcs.BooleanAnalysisChiSEmpty
import AFTD.Kb.Tcs.DecisionTree
import AFTD.Kb.Tcs.DecisionTreeEval
import AFTD.Kb.Tcs.DecisionTreeCoeffs
import AFTD.Kb.Tcs.DecisionTreeSignEval
import AFTD.Kb.Tcs.DecisionTreeChiSSymmDiffSingleton
import AFTD.Kb.Tcs.DecisionTreeSumSymmDiffReindex

/-!
# DecisionTree.signEval_eq_sum_coeffs

Topic: circuits   Node: 34cf759acec4

Provenance: helper lemma. TCSlib, `DecisionTree.signEval_eq_sum_coeffs`. Lean proof by Hydroxyi, Owen McGinty, Seyoon Ragavan (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/LMN/DecisionTreeFourier.lean (Apache-2.0); 1 verbatim; compiled here.

Walsh expansion of a decision tree's sign function. Let $T$ be a decision tree on $n$ Boolean variables, computing the $\pm 1$-valued
sign-encoded function $x \mapsto \sigma(T(x))$, where $\sigma$ is the sign encoding
sending $\mathrm{false}$ to $1$ and $\mathrm{true}$ to $-1$. For every point $x \in
\{0,1\}^n$,
\[
  \sigma(T(x)) \;=\; \sum_{S \subseteq [n]} c_T(S)\,\chi_S(x),
\]
where the sum ranges over all subsets $S$ of $[n]$, $c_T(S)$ denotes the recursively
defined coefficient of $T$ at the frequency $S$, and $\chi_S$ is the Walsh character of
$S$.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BooleanAnalysis in
variable {n : ℕ} in
/-- `signEval T = ∑_S coeffs T S · χ_S` pointwise. -/
lemma DecisionTree.signEval_eq_sum_coeffs (T : DecisionTree n) (x : BoolCube n) :
    T.signEval x = ∑ S : Finset (Fin n), T.coeffs S * chiS S x := by
  induction T with
  | leaf b =>
      simp [signEval, DecisionTree.eval, coeffs, ite_mul, Finset.sum_ite_eq', chiS_empty]
  | branch i lo hi ih_lo ih_hi =>
      have expand : ∑ S : Finset (Fin n), (DecisionTree.branch i lo hi).coeffs S * chiS S x
          = ((∑ S : Finset (Fin n), lo.coeffs S * chiS S x)
              + ∑ S : Finset (Fin n), hi.coeffs S * chiS S x) / 2
            + ((∑ S : Finset (Fin n), lo.coeffs S * chiS S x)
              - ∑ S : Finset (Fin n), hi.coeffs S * chiS S x) / 2 * boolToSign (x i) := by
        have step1 : ∑ S : Finset (Fin n), (DecisionTree.branch i lo hi).coeffs S * chiS S x
            = (∑ S : Finset (Fin n), (lo.coeffs S + hi.coeffs S) / 2 * chiS S x)
              + ∑ S : Finset (Fin n),
                (lo.coeffs (symmDiff S {i}) - hi.coeffs (symmDiff S {i})) / 2 * chiS S x := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun S _ => ?_
          simp only [coeffs]; ring
        have step2 : ∑ S : Finset (Fin n),
              (lo.coeffs (symmDiff S {i}) - hi.coeffs (symmDiff S {i})) / 2 * chiS S x
            = ∑ S : Finset (Fin n),
              (lo.coeffs S - hi.coeffs S) / 2 * chiS S x * boolToSign (x i) := by
          rw [← sum_symmDiff_reindex
            (fun S => (lo.coeffs S - hi.coeffs S) / 2 * chiS S x * boolToSign (x i)) i]
          refine Finset.sum_congr rfl fun S _ => ?_
          rw [chiS_symmDiff_singleton]
          cases x i <;> simp [boolToSign]
        have hA : ∑ S : Finset (Fin n), (lo.coeffs S + hi.coeffs S) / 2 * chiS S x
            = ((∑ S : Finset (Fin n), lo.coeffs S * chiS S x)
                + ∑ S : Finset (Fin n), hi.coeffs S * chiS S x) / 2 := by
          have hterm : ∀ S : Finset (Fin n), (lo.coeffs S + hi.coeffs S) / 2 * chiS S x
              = (lo.coeffs S * chiS S x + hi.coeffs S * chiS S x) / 2 := fun S => by ring
          rw [Finset.sum_congr rfl fun S _ => hterm S, ← Finset.sum_div,
            Finset.sum_add_distrib]
        have hB : ∑ S : Finset (Fin n),
              (lo.coeffs S - hi.coeffs S) / 2 * chiS S x * boolToSign (x i)
            = ((∑ S : Finset (Fin n), lo.coeffs S * chiS S x)
                - ∑ S : Finset (Fin n), hi.coeffs S * chiS S x) / 2 * boolToSign (x i) := by
          rw [← Finset.sum_mul]
          congr 1
          have hterm : ∀ S : Finset (Fin n), (lo.coeffs S - hi.coeffs S) / 2 * chiS S x
              = (lo.coeffs S * chiS S x - hi.coeffs S * chiS S x) / 2 := fun S => by ring
          rw [Finset.sum_congr rfl fun S _ => hterm S, ← Finset.sum_div,
            Finset.sum_sub_distrib]
        rw [step1, step2, hA, hB]
      rw [expand, ← ih_lo, ← ih_hi]
      simp only [signEval, DecisionTree.eval]
      cases hxi : x i <;> simp [boolToSign] <;> ring
