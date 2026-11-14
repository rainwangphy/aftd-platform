import AFTD.Prelude
import AFTD.Kb.Physics.EnergyFilterSequenceCentralBinomAsymptotic

/-!
# energy_filter_trace4_normalizer_limit

Topic: statistical_mechanics   Node: 005c0703b08d

Provenance: helper lemma. OP-892: algebraic conversion of the fourth-trace normalization.

The central-binomial normalization factor needed to convert the shifted fourth-trace limit to the original normalization tends to 2/√π.
-/

theorem energy_filter_trace4_normalizer_limit :
  Filter.Tendsto (fun k : ℕ =>
    ((Nat.choose (2 * k) k : ℝ) ^ 4 * Real.sqrt (k : ℝ)) *
      (2 * Real.pi ^ (3 / 2 : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ)) / (2 : ℝ) ^ (8 * k))
    Filter.atTop (nhds (2 / Real.sqrt Real.pi)) := by
  let X : ℕ → ℝ := fun k => (Nat.choose (2*k) k : ℝ) * Real.sqrt (Real.pi*(k:ℝ)) / (4:ℝ)^k
  have hX : Filter.Tendsto X Filter.atTop (nhds 1) := energy_filter_sequence_central_binom_asymptotic
  have ht := (hX.pow 4).mul_const (2 / Real.sqrt Real.pi)
  simp only [one_pow, one_mul] at ht
  apply ht.congr'
  filter_upwards [Filter.eventually_ge_atTop 1] with k hk
  have hkpos : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsqrtn : (Real.sqrt (k:ℝ))^2 = k := Real.sq_sqrt hkpos.le
  have hsqrtp : (Real.sqrt Real.pi)^2 = Real.pi := Real.sq_sqrt hpi.le
  have hsqrtpn : (Real.sqrt (Real.pi*(k:ℝ)))^2 = Real.pi*(k:ℝ) := Real.sq_sqrt (by positivity)
  have hthree (x : ℝ) (hx : 0 < x) : x ^ (3/2:ℝ) = x * Real.sqrt x := by
    rw [show (3/2:ℝ) = 1+1/2 by norm_num, Real.rpow_add hx, Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hpow : (2:ℝ)^(8*k) = ((4:ℝ)^k)^4 := by
    calc
      _ = ((2:ℝ)^8)^k := by rw [pow_mul]
      _ = ((4:ℝ)^4)^k := by norm_num
      _ = _ := by rw [← pow_mul, Nat.mul_comm, pow_mul]
  dsimp [X]
  rw [hthree Real.pi hpi, hthree (k:ℝ) hkpos, hpow]
  have hp : Real.sqrt Real.pi ≠ 0 := by positivity
  have hn : Real.sqrt (k:ℝ) ≠ 0 := by positivity
  have hpn : Real.sqrt (Real.pi*(k:ℝ)) ≠ 0 := by positivity
  have h4 : (4:ℝ)^k ≠ 0 := by positivity
  field_simp
  have h4pn : (Real.sqrt (Real.pi*(k:ℝ)))^4 = (Real.pi*(k:ℝ))^2 := by
    calc
      _ = ((Real.sqrt (Real.pi*(k:ℝ)))^2)^2 := by ring
      _ = _ := by rw [hsqrtpn]
  rw [h4pn, hsqrtp, hsqrtn]
  ring
