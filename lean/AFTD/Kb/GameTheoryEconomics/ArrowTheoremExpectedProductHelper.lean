import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremProfile
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremCorrFunc
import AFTD.Kb.Tcs.BooleanAnalysisBoolCube
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisChiS
import AFTD.Kb.Tcs.BooleanAnalysisFourierCoeff
import AFTD.Kb.Tcs.BooleanAnalysisWalshExpansion

/-!
# ArrowTheorem.expected_product_helper

Topic: social_choice   Node: e652389d5240

Provenance: helper lemma. TCSlib, `ArrowTheorem.expected_product_helper`. Lean proof by Mina, Allan Li, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/ArrowTheorem.lean (Apache-2.0); 1 verbatim; compiled here.

Expected product from the character kernel. Let $f:\{0,1\}^n\to\bbr$ be a Boolean function, and let
$\mathrm{votes}_1,\mathrm{votes}_2$ each assign to every profile
$p\in(\mathrm{Fin}\,6)^{\,n}$ a point of the Boolean hypercube $\{0,1\}^n$. Suppose the
pair satisfies the kernel identity
\[
\Bigl(\tfrac16\Bigr)^{\!n}\sum_{p}
\chi_S(\mathrm{votes}_1(p))\,\chi_T(\mathrm{votes}_2(p))
  \;=\; \begin{cases}(-1/3)^{|S|} & S = T,\\ 0 & S \ne T,\end{cases}
\]
for all $S,T\subseteq[n]$, where the sum runs over all $6^n$ profiles. Then
\[
  \Bigl(\tfrac16\Bigr)^{\!n}\sum_{p} f(\mathrm{votes}_1(p))\,f(\mathrm{votes}_2(p))
  \;=\; \mathrm{corr}(f)
  \;=\; \sum_{S\subseteq[n]} \hat f(S)^2\,(-1/3)^{|S|}.
\]
-/

set_option maxHeartbeats 800000 in
open scoped BigOperators in
open BooleanAnalysis in
variable {n : ℕ} in
/-- General helper: E[f(votes1) · f(votes2)] = corrFunc f, given a kernel. -/
lemma ArrowTheorem.expected_product_helper (f : BooleanFunc n)
    (votes1 votes2 : Profile n → BoolCube n)
    (hkernel : ∀ S T : Finset (Fin n),
      (1/6 : ℝ)^n * ∑ p : Profile n, chiS S (votes1 p) * chiS T (votes2 p) =
      if S = T then (-1/3 : ℝ)^S.card else 0) :
    (1/6 : ℝ)^n * ∑ p : Profile n, f (votes1 p) * f (votes2 p) = corrFunc f := by
  simp only [corrFunc]
  simp_rw [show ∀ p : Profile n, f (votes1 p) =
      ∑ S : Finset (Fin n), fourierCoeff f S * chiS S (votes1 p) from
    fun p => walsh_expansion f (votes1 p),
    show ∀ p : Profile n, f (votes2 p) =
      ∑ T : Finset (Fin n), fourierCoeff f T * chiS T (votes2 p) from
    fun p => walsh_expansion f (votes2 p)]
  -- Expand product of sums, keeping S as outer variable
  simp_rw [show ∀ p : Profile n,
      (∑ S : Finset (Fin n), fourierCoeff f S * chiS S (votes1 p)) *
      (∑ T : Finset (Fin n), fourierCoeff f T * chiS T (votes2 p)) =
      ∑ S : Finset (Fin n), ∑ T : Finset (Fin n),
        (fourierCoeff f S * chiS S (votes1 p)) * (fourierCoeff f T * chiS T (votes2 p)) from
    fun p => by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro S _
      rw [Finset.mul_sum]]
  -- Distribute (1/6)^n inside: ∑_p ∑_S ∑_T (fS*xS)*(fT*yT) → ∑_p ∑_S ∑_T (1/6)^n*(...)
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  -- Swap ∑_p ↔ ∑_S
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro S _
  -- Swap ∑_p ↔ ∑_T
  rw [Finset.sum_comm]
  -- Convert each (S,T)-block using the kernel
  trans (∑ T : Finset (Fin n), fourierCoeff f S * fourierCoeff f T *
      ((1/6 : ℝ)^n * ∑ p : Profile n, chiS S (votes1 p) * chiS T (votes2 p)))
  · apply Finset.sum_congr rfl; intro T _
    rw [← Finset.mul_sum]
    have hsumeq : ∑ p : Profile n,
          (fourierCoeff f S * chiS S (votes1 p)) * (fourierCoeff f T * chiS T (votes2 p)) =
        fourierCoeff f S * fourierCoeff f T *
          ∑ p : Profile n, chiS S (votes1 p) * chiS T (votes2 p) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring
    rw [hsumeq]; ring
  · -- Apply the kernel then collapse the diagonal sum
    simp_rw [hkernel]
    simp only [mul_ite, mul_zero]
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
    ring
