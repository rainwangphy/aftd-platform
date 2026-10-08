import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisSumBoolToSign
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSign
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSignMulSelf
import AFTD.Kb.Tcs.BooleanAnalysisChiSSingleton
import AFTD.Kb.Tcs.BooleanAnalysisBoolCube
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSignTrue
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSignFalse
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSignSq
import AFTD.Kb.Tcs.BooleanAnalysisChiS

/-!
# BooleanAnalysis.sum_chiS

Topic: combinatorics   Node: 6ff717958bed

Provenance: helper lemma. TCSlib, `BooleanAnalysis.sum_chiS`. Lean proof by Jingzhen Sha, Allan Li, Hydroxyi, Mina, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Basic.lean (Apache-2.0); 1 adapted; compiled here.

Sum of a Walsh character over the cube. Let $n$ be a natural number and let $S \subseteq [n]$. Summing the Walsh--Fourier
character $\chi_S$ over the entire Boolean hypercube $\{0,1\}^n$ gives
\[
  \sum_{x \in \{0,1\}^n} \chi_S(x) \;=\;
\begin{cases} 2^n & \text{if } S = \varnothing,\\ 0 & \text{if } S \ne \varnothing.
\end{cases}
\]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option maxHeartbeats 400000 in
open scoped BigOperators in
variable {n : ℕ} in
/-- Summing `χ_S` over the entire hypercube gives `2ⁿ` if `S = ∅`, else `0`. -/
lemma BooleanAnalysis.sum_chiS (S : Finset (Fin n)) :
    ∑ x : BoolCube n, chiS S x = if S = ∅ then 2 ^ n else 0 := by
  simp only [chiS]
  by_cases hS : S = ∅
  · subst hS; simp [Fintype.card_pi, Fintype.card_bool]
  · simp only [hS, if_false]
    have factored : ∑ x : BoolCube n, ∏ i ∈ S, boolToSign (x i) =
        ∑ x : BoolCube n, ∏ i : Fin n, (if i ∈ S then boolToSign (x i) else 1) := by
      congr 1; ext x; rw [← Finset.prod_filter]; simp
    rw [factored]
    -- Goal: ∑ x : BoolCube n, ∏ i : Fin n, g i (x i) = 0
    -- where g i b = if i ∈ S then boolToSign b else 1
    -- Factor: = ∏ i : Fin n, ∑ b : Bool, g i b  (by Fintype.prod_sum reversed)
    rw [show ∑ x : BoolCube n, ∏ i : Fin n, (if i ∈ S then boolToSign (x i) else 1) =
        ∏ i : Fin n, ∑ b : Bool, (if i ∈ S then boolToSign b else 1) from
      (Fintype.prod_sum (fun i b => if i ∈ S then boolToSign b else 1)).symm]
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi, boolToSign]
