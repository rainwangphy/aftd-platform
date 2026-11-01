import AFTD.Prelude

/-!
# concave_power_sum_le

Topic: quantum   Node: f0b876cefef7

Provenance: formalization of a published result. Source: arXiv:2610.35838 Appendix E, Fact 2

For non-negative real numbers p and q such that p^2 + q^2 <= 1, and any real r with 0 < r <= 1, the sum of powers satisfies p^r + q^r <= 2^(1 - r / 2).
-/

/-- Fact 2: Power sum inequality p^r + q^r <= 2^(1 - r/2) from concavity of t |-> t^(r/2). -/
theorem concave_power_sum_le
    (p q r : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p ^ 2 + q ^ 2 ≤ 1)
    (hr_pos : 0 < r) (hr_le : r ≤ 1) :
    p ^ r + q ^ r ≤ (2 : ℝ) ^ (1 - r / 2) := by
  set s := r / 2 with hs
  have hs_pos : 0 < s := by positivity
  have hs_nonneg : 0 ≤ s := le_of_lt hs_pos
  have hs_le : s ≤ 1 := by nlinarith
  have hconc := Real.concaveOn_rpow (p := s) hs_nonneg hs_le
  obtain ⟨_, hconc'⟩ := hconc
  have hconc_apply := hconc' (x := p ^ 2) (by simpa using sq_nonneg p)
    (y := q ^ 2) (by simpa using sq_nonneg q)
    (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num : (1 : ℝ) / 2 + 1 / 2 = 1)
  norm_num at hconc_apply
  rw [show (1 / 2 : ℝ) * p ^ 2 + 1 / 2 * q ^ 2 = (p ^ 2 + q ^ 2) / 2 by ring]
    at hconc_apply
  have hsum : p ^ r + q ^ r ≤ 2 * ((p ^ 2 + q ^ 2) / 2) ^ s := by
    rw [show r = ((2 : ℕ) : ℝ) * s by rw [hs]; norm_num; ring,
      Real.rpow_natCast_mul hp 2 s, Real.rpow_natCast_mul hq 2 s]
    linarith
  have hbase_nonneg : 0 ≤ (p ^ 2 + q ^ 2) / 2 := by positivity
  have hbase_le : (p ^ 2 + q ^ 2) / 2 ≤ 1 / 2 := by linarith
  have hmono : ((p ^ 2 + q ^ 2) / 2) ^ s ≤ (1 / 2 : ℝ) ^ s :=
    Real.rpow_le_rpow hbase_nonneg hbase_le hs_nonneg
  have hmul : 2 * ((p ^ 2 + q ^ 2) / 2) ^ s ≤ 2 * (1 / 2 : ℝ) ^ s := by
    nlinarith
  have htwo : 2 * (1 / 2 : ℝ) ^ s = 2 ^ (1 - s) := by
    rw [Real.div_rpow (by norm_num) (by norm_num)]
    norm_num
    rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) s]
    nth_rewrite 1 [← Real.rpow_one (2 : ℝ)]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2) 1 (-s)]
    ring_nf
  calc
    p ^ r + q ^ r ≤ 2 * ((p ^ 2 + q ^ 2) / 2) ^ s := hsum
    _ ≤ 2 * (1 / 2 : ℝ) ^ s := hmul
    _ = 2 ^ (1 - s) := htwo
    _ = (2 : ℝ) ^ (1 - r / 2) := by rw [hs]
