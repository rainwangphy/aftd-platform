import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBoolCube
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSign
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSignMulSelf
import AFTD.Kb.Tcs.BooleanAnalysisChiS

/-!
# BooleanAnalysis.chiS_mul_chiS

Topic: combinatorics   Node: 15e00dec8203

Provenance: helper lemma. TCSlib, `BooleanAnalysis.chiS_mul_chiS`. Lean proof by Jingzhen Sha, Allan Li, Hydroxyi, Mina, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Basic.lean (Apache-2.0); 1 adapted; compiled here.

Walsh characters multiply by symmetric difference. Fix $n$, and for a subset $S\subseteq[n]$ let $\chi_S\colon\{0,1\}^n\to\bbr$ denote the
associated Walsh--Fourier character. Then for all subsets $S,T\subseteq[n]$ and every
point $x\in\{0,1\}^n$,
\[
  \chi_S(x)\,\chi_T(x) \;=\; \chi_{S\,\triangle\,T}(x),
\]
where $S\,\triangle\,T$ is the symmetric difference of $S$ and $T$.
-/

set_option maxHeartbeats 400000 in
open scoped BigOperators in
variable {n : ℕ} in
/-- The pointwise product of two Walsh characters is another Walsh character (up to sign), specifically `χ_S · χ_T = χ_{S Δ T}` where `Δ` denotes symmetric difference. -/
lemma BooleanAnalysis.chiS_mul_chiS (S T : Finset (Fin n)) (x : BoolCube n) :
    (BooleanAnalysis.chiS S) x * (BooleanAnalysis.chiS T) x = (BooleanAnalysis.chiS (symmDiff S T)) x := by
  simp only [chiS]
  -- Decompose: S = (S \ T) ∪ (S ∩ T), T = (T \ S) ∪ (T ∩ S)
  have hS : ∏ i ∈ S, boolToSign (x i) =
      (∏ i ∈ S \ T, boolToSign (x i)) * ∏ i ∈ S ∩ T, boolToSign (x i) := by
    conv_lhs => rw [← Finset.sdiff_union_inter S T]
    apply Finset.prod_union
    simp only [Finset.disjoint_left, Finset.mem_sdiff, Finset.mem_inter, not_and]
    tauto
  have hT : ∏ i ∈ T, boolToSign (x i) =
      (∏ i ∈ T \ S, boolToSign (x i)) * ∏ i ∈ S ∩ T, boolToSign (x i) := by
    conv_lhs => rw [← Finset.sdiff_union_inter T S]
    rw [Finset.inter_comm T S]
    apply Finset.prod_union
    simp only [Finset.disjoint_left, Finset.mem_sdiff, Finset.mem_inter, not_and]
    tauto
  -- The intersection product squares to 1
  have hcancel : (∏ i ∈ S ∩ T, boolToSign (x i)) * ∏ i ∈ S ∩ T, boolToSign (x i) = 1 := by
    rw [← Finset.prod_mul_distrib]; simp [boolToSign_mul_self]
  rw [hS, hT, symmDiff_def, Finset.sup_eq_union, Finset.prod_union disjoint_sdiff_sdiff]
  -- Goal: (A * P) * (B * P) = A * B  where P² = 1
  set P := ∏ i ∈ S ∩ T, boolToSign (x i)
  set A := ∏ i ∈ S \ T, boolToSign (x i)
  set B := ∏ i ∈ T \ S, boolToSign (x i)
  calc A * P * (B * P) = A * B * (P * P) := by ring
    _ = A * B * 1 := by rw [hcancel]
    _ = A * B := by ring
