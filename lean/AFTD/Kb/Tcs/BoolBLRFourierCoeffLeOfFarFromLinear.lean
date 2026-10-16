import AFTD.Prelude
import AFTD.Kb.Tcs.BoolBLREpsilonFarFromLinear
import AFTD.Kb.Tcs.BoolBLRFourierCoeffLeOfDistGe
import AFTD.Kb.Tcs.BoolBLRIsLinearBool
import AFTD.Kb.Tcs.BoolBLRLiftPm1
import AFTD.Kb.Tcs.BoolBLRLinearBoolIffCharacter
import AFTD.Kb.Tcs.BoolFourierCharS
import AFTD.Kb.Tcs.BoolFourierFourierCoeff
import AFTD.Kb.Tcs.BoolFourierHypercube
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSignFalse
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSignTrue
import AFTD.Kb.Tcs.BooleanAnalysisChiS
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSign
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSignSq
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSignMulSelf
import AFTD.Kb.Tcs.BooleanAnalysisChiSSingleton
import AFTD.Kb.Tcs.BooleanAnalysisSumBoolToSign
import AFTD.Kb.Tcs.BooleanAnalysisInnerProductChiSelf
import AFTD.Kb.Tcs.BooleanAnalysisFlipBitFlipBit
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSignNot
import AFTD.Kb.Tcs.BooleanAnalysisInstAddCommGroupBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisInstModuleRealBooleanFunc
import AFTD.Kb.Tcs.BoolFourierBoolFun
import AFTD.Kb.Tcs.BoolFourierBoolToPM1
import AFTD.Kb.Tcs.BoolBLRBoolDist
import AFTD.Kb.Tcs.BooleanAnalysisBoolCube

/-!
# BoolBLR.fourier_coeff_le_of_far_from_linear

Topic: interactive   Node: 01b9f9b0c75a

Provenance: helper lemma. TCSlib, `BoolBLR.fourier_coeff_le_of_far_from_linear`. Lean proof by Prastik Mohanraj, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/BLR/BoolBLR.lean (Copyright (c) 2026 Prastik Mohanraj. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Fourier coefficient bound for functions far from linear. Let $f : \{0,1\}^n \to \{0,1\}$ be $\varepsilon$-far from linear, meaning that $0 \le
\varepsilon \le 1$ and every linear function $g : \{0,1\}^n \to \{0,1\}$ (one satisfying
$g(x \oplus y) = g(x) \oplus g(y)$ for all $x,y$) has $\Pr_{x}[f(x) \ne g(x)] \ge
\varepsilon$ under the uniform distribution. Let $F(x) = (-1)^{f(x)}$ be the $\pm 1$
lift of $f$. Then for every subset $S \subseteq [n]$, the Fourier coefficient of $F$ at
$S$ satisfies
\[
  \hat F(S) \;=\; \E_{x}\bigl[F(x)\,\chi_S(x)\bigr] \;\le\; 1 - 2\varepsilon,
\]
where $\chi_S(x) = \prod_{i \in S}(-1)^{x_i}$ is the Walsh character indexed by $S$.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BoolFourier in
/-- Bounds every Fourier coefficient of a function far from all linear functions. **Source:** [OD14, §1.6 (Fourier soundness proof)]. -/
lemma BoolBLR.fourier_coeff_le_of_far_from_linear
    {n : ℕ}
    (f : hypercube n → Bool)
    (ε : ℝ)
    (hfar : epsilon_far_from_linear f ε) :
    ∀ S : Finset (Fin n),
      fourier_coeff (lift_pm1 f) S ≤ 1 - 2 * ε := by
  intro S
  -- Build a linear g whose ±1 lift equals χ_S, witnessing closeness to χ_S.
  obtain ⟨g, hg⟩ : ∃ g : hypercube n → Bool, is_linear_bool g ∧ (lift_pm1 g) = (char_S S) := by
    -- First, exhibit g as parity over coordinates in S.
    obtain ⟨g, hg⟩ : ∃ g : hypercube n → Bool, lift_pm1 g = char_S S := by
      use fun x => (S.filter (fun i => x i)).card % 2 = 1;
      funext x; simp only [lift_pm1, char_S];
      -- Induction on S to compare parity-of-count vs product of (-1)^{x_i}.
      induction S using Finset.induction with
      | empty => simp [BooleanAnalysis.chiS, BooleanAnalysis.boolToSign]
      | insert a s ha ih =>
        simp only [BooleanAnalysis.chiS] at ih ⊢
        rw [Finset.prod_insert ha, ← ih, Finset.filter_insert]
        by_cases hx : x a = true
        · rw [if_pos hx, Finset.card_insert_of_notMem (fun h => ha (Finset.mem_filter.mp h).1)]
          rcases Nat.mod_two_eq_zero_or_one (s.filter (fun i => x i = true)).card with h | h <;>
            simp [h, Nat.add_mod, hx, BooleanAnalysis.boolToSign]
        · simp [hx, BooleanAnalysis.boolToSign]
    -- Then use linear_bool_iff_character to conclude g is linear.
    exact ⟨ g, by exact linear_bool_iff_character g |>.2 ⟨ S, hg ⟩, hg ⟩;
  -- Apply the previous lemma using the ε-farness from this specific linear g.
  exact fourier_coeff_le_of_dist_ge f g S hg.2 ( hfar.2.2 g hg.1 )

-- if f is epsilon-far from all linear functions, then the sum of cubes term is ≤ 1 - 2 * ε
