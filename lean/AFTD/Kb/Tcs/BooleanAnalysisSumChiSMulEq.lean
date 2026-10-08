import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBoolCube
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSign
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSignMulSelf
import AFTD.Kb.Tcs.BooleanAnalysisChiS
import AFTD.Kb.Tcs.BooleanAnalysisSumProdSubsetEqProdOneAdd

/-!
# BooleanAnalysis.sum_chiS_mul_eq

Topic: combinatorics   Node: 436fd168952f

Provenance: helper lemma. TCSlib, `BooleanAnalysis.sum_chiS_mul_eq`. Lean proof by Jingzhen Sha, Allan Li, Hydroxyi, Mina, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Basic.lean (Apache-2.0); 1 verbatim; compiled here.

Completeness kernel for the Walsh basis. Let $x, y \in \{0,1\}^n$ be points of the Boolean hypercube. Then the sum of the
products of Walsh--Fourier characters over all subsets of $[n]$ satisfies
\[
  \sum_{S \subseteq [n]} \chi_S(x)\,\chi_S(y) \;=\;
  \begin{cases} 2^n & \text{if } x = y,\\[2pt] 0 & \text{if } x \neq y. \end{cases}
\]
-/

set_option maxHeartbeats 400000 in
open scoped BigOperators in
variable {n : ℕ} in
/-- The sum of `χ_S(x) * χ_S(y)` over all `S ⊆ [n]` equals `2ⁿ` if `x = y`, else `0`. This is the completeness kernel for the Walsh basis. -/
lemma BooleanAnalysis.sum_chiS_mul_eq (x y : BoolCube n) :
    ∑ S : Finset (Fin n), chiS S x * chiS S y = if x = y then (2 : ℝ) ^ n else 0 := by
  simp only [chiS, ← Finset.prod_mul_distrib]
  rw [sum_prod_subset_eq_prod_one_add]
  split_ifs with hxy
  · subst hxy; simp only [boolToSign_mul_self]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    norm_num
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    have : boolToSign (x i) * boolToSign (y i) = -1 := by
      cases hxi : x i <;> cases hyi : y i <;> simp_all [boolToSign]
    simp [this]
