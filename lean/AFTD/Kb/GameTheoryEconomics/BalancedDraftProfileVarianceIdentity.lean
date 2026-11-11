import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BalancedDraftProfileSquareIntegral
import AFTD.Kb.GameTheoryEconomics.BalancedDraftAsymptoticVariance

/-!
# balanced_draft_profile_variance_identity

Topic: fair_division   Node: 706040c26fbe

Provenance: helper lemma. Variance calculation in the one-agent limit of OP-1493.

The variance obtained from the squared threshold profile, the fraction of other turns, and the variance of a centered uniform variable equals the proposed balanced-draft asymptotic variance.
-/

open MeasureTheory intervalIntegral

theorem balanced_draft_profile_variance_identity (n : ℕ) (hn : 2 ≤ n) :
    (16*(n:ℝ)^2/((n:ℝ)+1)^2) * (((n:ℝ)-1)/(n:ℝ)) * (1/12:ℝ) *
      (∫ x : ℝ in (0:ℝ)..1, (1-x) ^ ((2:ℝ)/(n:ℝ))) =
      balanced_draft_asymptotic_variance n := by
  rw [balanced_draft_profile_square_integral n hn]
  unfold balanced_draft_asymptotic_variance
  have hnpos : (0:ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hn)
  have hn0 : (n:ℝ) ≠ 0 := ne_of_gt hnpos
  have h1 : (n:ℝ)+1 ≠ 0 := by positivity
  have h2 : (n:ℝ)+2 ≠ 0 := by positivity
  field_simp
  ring
