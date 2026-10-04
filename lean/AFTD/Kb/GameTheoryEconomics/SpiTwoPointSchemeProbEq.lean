import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiTwoPointMaxProb
import AFTD.Kb.GameTheoryEconomics.SpiTwoPointPoolProb
import AFTD.Kb.GameTheoryEconomics.SpiTwoPointPoolProbMem
import AFTD.Kb.GameTheoryEconomics.SpiIteNullSignal
import AFTD.Kb.GameTheoryEconomics.SpiTwoPointScheme

/-!
# spi_two_point_scheme_prob_eq

Topic: mechanism_design   Node: d0ef36912648

Real-arithmetic part of the optimality of the two-point scheme: its two signals give acceptance probability exactly spi_two_point_max_prob.
-/

/-- Real-arithmetic part of the optimality of `spi_two_point_scheme`: the accepted probability of its two signals (signal 0 with mass `q + (1-q) β`, signal 1 with mass `(1-q)(1-β)` and posterior mean `l`) equals `spi_two_point_max_prob`. -/
lemma spi_two_point_scheme_prob_eq (h l q T : ℝ) (hlh : l ≤ h) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (if T * (q * 1 + (1 - q) * spi_two_point_pool_prob h l q T) ≤
        q * 1 * h + (1 - q) * spi_two_point_pool_prob h l q T * l
      then q * 1 + (1 - q) * spi_two_point_pool_prob h l q T else 0) +
    (if T * ((1 - q) * (1 - spi_two_point_pool_prob h l q T)) ≤
        (1 - q) * (1 - spi_two_point_pool_prob h l q T) * l
      then (1 - q) * (1 - spi_two_point_pool_prob h l q T) else 0) =
    spi_two_point_max_prob h l q T := by
  have hmem := spi_two_point_pool_prob_mem h l q T hlh hq0 hq1
  set β := spi_two_point_pool_prob h l q T with hβ
  unfold spi_two_point_max_prob
  unfold spi_two_point_pool_prob at hβ
  by_cases h1 : T ≤ q * h + (1 - q) * l
  · rw [if_pos h1] at hβ ⊢
    rw [hβ, if_pos (by linarith)]
    simp
  · rw [if_neg h1] at hβ ⊢
    by_cases h2 : T ≤ h
    · rw [if_pos h2] at hβ ⊢
      have hq1' : q < 1 := by
        by_contra hc; push Not at hc
        have e : q * h + (1 - q) * l = h := by rw [le_antisymm hq1 hc]; ring
        linarith
      have hTl : 0 < T - l := by nlinarith
      have h1q : 0 < 1 - q := by linarith
      have hm0 : q * 1 + (1 - q) * β = q * (h - l) / (T - l) := by
        rw [hβ]; field_simp; ring
      have hv0 : q * 1 * h + (1 - q) * β * l = T * (q * (h - l) / (T - l)) := by
        rw [hβ]; field_simp; ring
      rw [hm0, hv0, if_pos le_rfl,
        spi_ite_null_signal T ((1 - q) * (1 - β)) l (mul_nonneg h1q.le (by linarith [hmem.2])) (by linarith)]
      ring
    · rw [if_neg h2] at hβ ⊢
      rw [hβ]
      simp only [mul_zero, zero_mul, add_zero, mul_one, sub_zero]
      rw [spi_ite_null_signal T q h hq0 (by linarith),
        spi_ite_null_signal T (1 - q) l (by linarith) (by linarith)]
      ring
