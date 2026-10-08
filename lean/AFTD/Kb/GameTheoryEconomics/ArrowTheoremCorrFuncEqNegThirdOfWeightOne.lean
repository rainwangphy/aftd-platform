import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremCorrFunc
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisFourierCoeff
import AFTD.Kb.Tcs.BooleanAnalysisFourierCoeffOddEven
import AFTD.Kb.Tcs.BooleanAnalysisIsOddFunc
import AFTD.Kb.Tcs.BooleanAnalysisIsPmOne
import AFTD.Kb.Tcs.BooleanAnalysisParsevalPmOne

/-!
# ArrowTheorem.corrFunc_eq_neg_third_of_weight_one

Topic: social_choice   Node: 750131ad3249

Provenance: helper lemma. TCSlib, `ArrowTheorem.corrFunc_eq_neg_third_of_weight_one`. Lean proof by Mina, Allan Li, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/ArrowTheorem.lean (Apache-2.0); 1 verbatim; compiled here.

Extremal correlation concentrates weight on level one. Let $f:\{0,1\}^n\to\bbr$ be a $\pm 1$-valued Boolean function that is odd, meaning
$f(\lnot x)=-f(x)$ for every $x$, and suppose its Fourier correlation function attains
the value
\[
  \mathrm{corr}(f)\;=\;\sum_{S\subseteq[n]}\hat f(S)^2\,(-1/3)^{|S|}\;=\;-\tfrac13.
\]
Then $\hat f(S)=0$ for every subset $S\subseteq[n]$ with $|S|\neq 1$; that is, all
Fourier--Walsh weight of $f$ is carried by the singleton frequencies.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option maxHeartbeats 800000 in
open scoped BigOperators in
open BooleanAnalysis in
variable {n : ℕ} in
/-- If the correlation function equals -1/3, then f̂(S) = 0 for all S with |S| ≥ 3 (i.e., all Fourier weight is on levels 0 and 1). Since f is odd, f̂(∅) = f̂(S for even |S|) = 0. So in fact all Fourier weight is on level 1. -/
lemma ArrowTheorem.corrFunc_eq_neg_third_of_weight_one {f : BooleanFunc n}
    (hodd : isOddFunc f) (hpm : isPmOne f) (hcorr : corrFunc f = -1/3) :
    ∀ S : Finset (Fin n), S.card ≠ 1 → fourierCoeff f S = 0 := by
  intro S hS
  -- From hcorr = -1/3 and the lower bound, the sum equals its lower bound,
  -- so each term achieves equality.
  -- The lower bound analysis: ∑ f̂(S)² [(-1/3)^|S| - (-1/3)] = 0.
  -- Since f̂(S)² ≥ 0 and (-1/3)^|S| - (-1/3) ≥ 0 for odd |S| ≥ 3,
  -- each such term must be zero.
  by_cases heven : Even S.card
  · exact fourierCoeff_odd_even f hodd S heven
  · -- |S| is odd
    rw [Nat.not_even_iff_odd] at heven
    -- If |S| = 1, we're done
    by_cases hcard : S.card = 1
    · exact absurd hcard hS
    · -- |S| is odd and ≠ 1, so |S| ≥ 3
      -- The equality condition forces f̂(S) = 0
      obtain ⟨k, hk⟩ := heven  -- S.card = 2*k+1
      have hge3 : S.card ≥ 3 := by omega
      -- We use the equality condition from the sum lower bound
      have hzero : fourierCoeff f S ^ 2 * ((-1/3 : ℝ) ^ S.card - (-1/3)) = 0 := by
        -- The sum ∑ f̂(T)² [(-1/3)^|T| - (-1/3)] = 0
        -- because ∑ f̂(T)² (-1/3)^|T| = -1/3 = (-1/3) ∑ f̂(T)²
        have hsum : ∑ T : Finset (Fin n),
            fourierCoeff f T ^ 2 * ((-1/3 : ℝ) ^ T.card - (-1/3)) = 0 := by
          have hpars := parseval_pm_one f hpm
          simp only [corrFunc] at hcorr
          simp_rw [mul_sub]
          rw [Finset.sum_sub_distrib, hcorr,
              show ∑ T : Finset (Fin n), fourierCoeff f T ^ 2 * (-1/3 : ℝ) =
                  (-1/3) * ∑ T : Finset (Fin n), fourierCoeff f T ^ 2 from by
                rw [Finset.mul_sum]; congr 1; ext T; ring,
              hpars]
          ring
        -- Each term in the sum is nonneg (so each must be zero)
        have hterm_nonneg : ∀ T : Finset (Fin n),
            fourierCoeff f T ^ 2 * ((-1/3 : ℝ) ^ T.card - (-1/3)) ≥ 0 := by
          intro T
          by_cases hT_even : Even T.card
          · -- even: f̂(T) = 0, whole term is 0
            have hzeroT : fourierCoeff f T = 0 := fourierCoeff_odd_even f hodd T hT_even
            simp [hzeroT]
          · -- odd: (-1/3)^|T| ≥ -1/3
            apply mul_nonneg (sq_nonneg _)
            rw [Nat.not_even_iff_odd] at hT_even
            obtain ⟨j, hj⟩ := hT_even
            have hge : (-1/3 : ℝ) ^ T.card ≥ -1/3 := by
              rw [hj, show (-1/3 : ℝ) = -(1/3 : ℝ) from by norm_num]
              have hodd_n : Odd (2 * j + 1) := ⟨j, rfl⟩
              rw [hodd_n.neg_pow]
              have hle : (1/3 : ℝ) ^ (2*j+1) ≤ 1/3 := by
                have := pow_le_pow_of_le_one (by positivity : (0:ℝ) ≤ 1/3)
                          (by norm_num : (1/3:ℝ) ≤ 1) (show 1 ≤ 2*j+1 from by omega)
                simpa [pow_one] using this
              linarith
            linarith
        exact Finset.sum_eq_zero_iff_of_nonneg (fun T _ => hterm_nonneg T) |>.mp hsum
            S (Finset.mem_univ S)
      -- Extract f̂(S) = 0 from the product being zero
      have hfact_pos : (-1/3 : ℝ) ^ S.card - (-1/3) > 0 := by
        -- |S| ≥ 3 and odd: (-1/3)^|S| > -1/3 strictly
        have hk3 : k ≥ 1 := by omega
        rw [hk, show (-1/3 : ℝ) = -(1/3 : ℝ) from by norm_num]
        have hodd_n : Odd (2 * k + 1) := ⟨k, rfl⟩
        rw [hodd_n.neg_pow]
        -- Need: -(1/3)^(2*k+1) + 1/3 > 0, i.e., (1/3)^(2*k+1) < 1/3
        -- Bound: (1/3)^(2*k+1) ≤ (1/3)^3 = 1/27 < 1/3
        have hle : (1/3 : ℝ) ^ (2*k+1) ≤ 1/27 := by
          have h1 : (1/3 : ℝ) ^ (2*k+1) ≤ (1/3 : ℝ) ^ 3 :=
            pow_le_pow_of_le_one (by positivity) (by norm_num) (by omega)
          have h2 : (1/3 : ℝ) ^ 3 = 1/27 := by norm_num
          linarith
        linarith [show (1/27 : ℝ) < 1/3 from by norm_num]
      have := mul_eq_zero.mp hzero
      rcases this with h | h
      · exact pow_eq_zero_iff (by norm_num) |>.mp h
      · linarith
