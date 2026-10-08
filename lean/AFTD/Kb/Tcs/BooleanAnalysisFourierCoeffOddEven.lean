import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisUniformWeight
import AFTD.Kb.Tcs.BooleanAnalysisFourierCoeff
import AFTD.Kb.Tcs.BooleanAnalysisChiSNeg
import AFTD.Kb.Tcs.BooleanAnalysisIsOddFunc
import AFTD.Kb.Tcs.BooleanAnalysisBoolCube
import AFTD.Kb.Tcs.BooleanAnalysisChiS
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc

/-!
# BooleanAnalysis.fourierCoeff_odd_even

Topic: combinatorics   Node: e652779981c6

Provenance: helper lemma. TCSlib, `BooleanAnalysis.fourierCoeff_odd_even`. Lean proof by Jingzhen Sha, Allan Li, Hydroxyi, Mina, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Basic.lean (Apache-2.0); 1 verbatim; compiled here.

Vanishing of even-level Fourier coefficients of odd functions. Let $f : \{0,1\}^n \to \bbr$ be an odd Boolean function, meaning $f(\lnot x) = -f(x)$
for every $x \in \{0,1\}^n$, where $\lnot x$ denotes the pointwise negation of $x$. Then
for every subset $S \subseteq [n]$ of even cardinality, the Fourier--Walsh coefficient
of $f$ at $S$ vanishes: $\hat f(S) = 0$.
-/

set_option maxHeartbeats 400000 in
open scoped BigOperators in
variable {n : ℕ} in
/-- For an odd function, the Fourier coefficient at any even-cardinality set is zero. -/
lemma BooleanAnalysis.fourierCoeff_odd_even (f : BooleanFunc n) (hodd : isOddFunc f)
    (S : Finset (Fin n)) (heven : Even S.card) :
    fourierCoeff f S = 0 := by
  simp only [fourierCoeff, innerProduct, expect, uniformWeight]
  suffices h : ∑ x : BoolCube n, f x * chiS S x = 0 by simp [h]
  -- The bijection that flips all bits
  let e : BoolCube n ≃ BoolCube n :=
    { toFun    := fun x i => !x i
      invFun   := fun x i => !x i
      left_inv := fun x => by ext; simp
      right_inv := fun x => by ext; simp }
  -- Change of variables: ∑_x f(x) χ_S(x) = ∑_x f(¬x) χ_S(¬x)
  -- Uses that x ↦ (¬x) is a bijection (involution)
  have hcv : ∑ x : BoolCube n, f x * chiS S x =
      ∑ x : BoolCube n, f (fun i => !x i) * chiS S (fun i => !x i) :=
    (Fintype.sum_equiv e
      (fun x => f (fun i => !x i) * chiS S (fun i => !x i))
      (fun x => f x * chiS S x)
      (fun _ => rfl)).symm
  -- Apply oddness and chiS_neg
  have hflip : ∑ x : BoolCube n, f (fun i => !x i) * chiS S (fun i => !x i) =
      -(∑ x : BoolCube n, f x * chiS S x) := by
    -- Expose the universal form so simp_rw can use hodd
    have hodd' : ∀ x : BoolCube n, f (fun i => !x i) = -f x := hodd
    -- (-1)^|S| = 1 when |S| is even
    have hone : (-1 : ℝ) ^ S.card = 1 := by
      obtain ⟨k, hk⟩ := heven
      rw [hk, ← two_mul, pow_mul, show (-1 : ℝ) ^ 2 = 1 from by norm_num, one_pow]
    simp_rw [hodd', chiS_neg, hone, one_mul, neg_mul]
    simp [Finset.sum_neg_distrib]
  linarith [hcv.trans hflip]
