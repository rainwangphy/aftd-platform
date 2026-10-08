import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremProfile
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremAbVotes
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremAcyclic
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremBcVotes
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremCaVotes
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremCorrFunc
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremExpectedProductEqCorrFunc
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremExpectedProductAbca
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremExpectedProductBcca
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisIsOddFunc
import AFTD.Kb.Tcs.BooleanAnalysisIsPmOne

/-!
# ArrowTheorem.acyclic_implies_corrFunc

Topic: social_choice   Node: e0d1418e8da3

Provenance: helper lemma. TCSlib, `ArrowTheorem.acyclic_implies_corrFunc`. Lean proof by Mina, Allan Li, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/ArrowTheorem.lean (Apache-2.0); 1 verbatim; compiled here.

Acyclicity forces correlation $-1/3$. Let $f:\{0,1\}^n\to\bbr$ be a Boolean function that is odd, $\pm 1$-valued, and acyclic.
Then its Fourier correlation function satisfies
\[
  \mathrm{corr}(f)\;=\;\sum_{S\subseteq[n]}\hat f(S)^2\,(-1/3)^{|S|}\;=\;-\tfrac{1}{3}.
\]
-/

set_option maxHeartbeats 800000 in
open scoped BigOperators in
open BooleanAnalysis in
variable {n : ℕ} in
/-- Acyclicity of f implies that the Fourier correlation function equals -1/3. Key steps: 1. For any ±1 triple (a,b,c) avoiding (1,1,1) and (-1,-1,-1), ab+bc+ac = -1. 2. Summing over all 6^n profiles: ∑_p (f(ab)f(bc)+f(bc)f(ca)+f(ab)f(ca)) = -6^n. 3. The three pairwise expectations each equal corrFunc f. 4. Combining: 3·corrFunc f = -1, so corrFunc f = -1/3. **Source:** [OD14, Ch. 2]. -/
lemma ArrowTheorem.acyclic_implies_corrFunc (f : BooleanFunc n) (_hodd : isOddFunc f) (hpm : isPmOne f)
    (hacyc : acyclic f) : corrFunc f = -1/3 := by
  -- Step 1: per-profile, the three products sum to -1
  have hprod : ∀ p : Profile n,
      f (abVotes p) * f (bcVotes p) +
      f (bcVotes p) * f (caVotes p) +
      f (abVotes p) * f (caVotes p) = -1 := by
    intro p
    obtain ⟨hcyc1, hcyc2⟩ := hacyc p
    rcases hpm (abVotes p) with ha | ha <;>
    rcases hpm (bcVotes p) with hb | hb <;>
    rcases hpm (caVotes p) with hc | hc
    · exact absurd ⟨ha, hb, hc⟩ hcyc1
    · rw [ha, hb, hc]; norm_num
    · rw [ha, hb, hc]; norm_num
    · rw [ha, hb, hc]; norm_num
    · rw [ha, hb, hc]; norm_num
    · rw [ha, hb, hc]; norm_num
    · rw [ha, hb, hc]; norm_num
    · exact absurd ⟨ha, hb, hc⟩ hcyc2
  -- Step 2: (1/6)^n * ∑_p (sum of products) = 3 * corrFunc f
  have hkey : (1/6 : ℝ)^n * ∑ p : Profile n,
      (f (abVotes p) * f (bcVotes p) +
       f (bcVotes p) * f (caVotes p) +
       f (abVotes p) * f (caVotes p)) = 3 * corrFunc f := by
    simp_rw [Finset.sum_add_distrib]
    rw [mul_add, mul_add,
        expected_product_eq_corrFunc f,
        expected_product_bcca f,
        expected_product_abca f]
    ring
  -- Step 3: (1/6)^n * ∑_p (sum of products) = -1 (from hprod)
  have hval : (1/6 : ℝ)^n * ∑ p : Profile n,
      (f (abVotes p) * f (bcVotes p) +
       f (bcVotes p) * f (caVotes p) +
       f (abVotes p) * f (caVotes p)) = -1 := by
    simp_rw [hprod]
    have hn : Fintype.card (Profile n) = 6^n := by
      simp [Fintype.card_pi, Fintype.card_fin, Finset.prod_const, Finset.card_univ]
    rw [Finset.sum_const, Finset.card_univ, hn, nsmul_eq_mul]
    push_cast
    have h : (1 / 6 : ℝ) ^ n * (6 : ℝ) ^ n = 1 := by rw [← mul_pow]; norm_num
    linarith [mul_neg ((1 / 6 : ℝ) ^ n) ((6 : ℝ) ^ n)]
  -- Combine
  linarith
