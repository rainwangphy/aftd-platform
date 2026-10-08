import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisUniformWeight
import AFTD.Kb.Tcs.BooleanAnalysisFourierCoeffChi
import AFTD.Kb.Tcs.BooleanAnalysisFourierCoeff
import AFTD.Kb.Tcs.BooleanAnalysisChiSSingleton
import AFTD.Kb.Tcs.BooleanAnalysisInnerProductChiSelf
import AFTD.Kb.Tcs.BooleanAnalysisBoolCube
import AFTD.Kb.Tcs.BooleanAnalysisInnerProduct
import AFTD.Kb.Tcs.BooleanAnalysisChiS
import AFTD.Kb.Tcs.BooleanAnalysisFlipBitFlipBit

/-!
# DecisionTree.fourierCoeff_sum_chiS

Topic: circuits   Node: dd60cdad7431

Provenance: helper lemma. TCSlib, `DecisionTree.fourierCoeff_sum_chiS`. Lean proof by Hydroxyi, Owen McGinty, Seyoon Ragavan (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/LMN/DecisionTreeFourier.lean (Apache-2.0); 1 verbatim; compiled here.

Recovery of coefficients from a character expansion. Fix $n$, let $c$ assign a real number $c(S)$ to each subset $S \subseteq [n]$, and
consider the Boolean function $f(x) = \sum_{S \subseteq [n]} c(S)\,\chi_S(x)$, where
$\chi_S$ is the Walsh--Fourier character of $S$. Then for every $T \subseteq [n]$ the
Fourier--Walsh coefficient of $f$ at frequency $T$ recovers the corresponding
coefficient, namely $\hat f(T) = c(T)$.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BooleanAnalysis in
variable {n : ℕ} in
/-- The Fourier coefficient of an explicit character combination reads off the coefficient (uniqueness of the Fourier expansion). -/
lemma DecisionTree.fourierCoeff_sum_chiS (c : Finset (Fin n) → ℝ) (T : Finset (Fin n)) :
    fourierCoeff (fun x => ∑ S : Finset (Fin n), c S * chiS S x) T = c T := by
  have expand : fourierCoeff (fun x => ∑ S : Finset (Fin n), c S * chiS S x) T
      = ∑ S : Finset (Fin n), c S * innerProduct (chiS S) (chiS T) := by
    show uniformWeight n * ∑ x : BoolCube n,
        (∑ S : Finset (Fin n), c S * chiS S x) * chiS T x
      = ∑ S : Finset (Fin n),
          c S * (uniformWeight n * ∑ x : BoolCube n, chiS S x * chiS T x)
    calc uniformWeight n * ∑ x : BoolCube n,
            (∑ S : Finset (Fin n), c S * chiS S x) * chiS T x
        = uniformWeight n * ∑ x : BoolCube n,
            ∑ S : Finset (Fin n), c S * (chiS S x * chiS T x) := by
          congr 1
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun S _ => by ring
      _ = uniformWeight n * ∑ S : Finset (Fin n),
            ∑ x : BoolCube n, c S * (chiS S x * chiS T x) := by
          rw [Finset.sum_comm]
      _ = ∑ S : Finset (Fin n),
            c S * (uniformWeight n * ∑ x : BoolCube n, chiS S x * chiS T x) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun S _ => ?_
          rw [← Finset.mul_sum]
          ring
  rw [expand]
  have hterm : ∀ S : Finset (Fin n),
      c S * innerProduct (chiS S) (chiS T) = if S = T then c S else 0 := by
    intro S
    rw [BooleanAnalysis.fourier_coeff_chi]
    split_ifs <;> simp
  simp only [hterm]
  simp
