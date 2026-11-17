import AFTD.Prelude
import AFTD.Kb.Physics.DyadicPhaseEnvelope

/-!
# fermion_pair_phase_envelope_s2_upper_bound

Topic: quantum_mechanics   Node: 6ae78bc7f630

Provenance: formalization of a published result. Source: arXiv:2611.07003; OP-1787

For s = 2 with p = 1/5 and q = 4/5, for all real t such that 1 <= t and t <= 2, dyadic_phase_envelope 2 t / Real.sqrt (2 * Real.pi * p * q) <= 27 / (4 * Real.sqrt (2 * Real.pi)).
-/

open Finset

lemma fermion_pair_phase_envelope_s2_upper_bound_j0 (y : ℝ) (hy1 : 1 / 15 ≤ y) (hy2 : y < 16 / 15) :
    dyadic_phase_envelope.S 2 y = y + 4 / 15 := by
  dsimp [dyadic_phase_envelope.S]
  have hlog16 : 0 < Real.log 16 := Real.log_pos (by norm_num)
  have hpos : 0 < y * 15 := by linarith
  have h1 : 0 ≤ Real.log (y * 15) / Real.log 16 := by
    have : 1 ≤ y * 15 := by linarith
    have hlog : 0 ≤ Real.log (y * 15) := Real.log_nonneg this
    exact div_nonneg hlog (le_of_lt hlog16)
  have h2 : Real.log (y * 15) / Real.log 16 < 1 := by
    rw [div_lt_iff₀ hlog16]
    have : y * 15 < 16 := by linarith
    rw [one_mul]
    exact Real.log_lt_log hpos this
  have hcalc1 : ((2 : ℝ) ^ 2) ^ 2 - 1 = 15 := by norm_num
  have hcalc2 : ((2 : ℝ) ^ 2) ^ 2 = 16 := by norm_num
  have hj : ⌊Real.log (y * (((2 : ℝ) ^ 2) ^ 2 - 1)) / Real.log (((2 : ℝ) ^ 2) ^ 2)⌋ = (0 : ℤ) := by
    rw [hcalc1, hcalc2]
    rw [Int.floor_eq_iff]
    push_cast
    exact ⟨h1, by linarith⟩
  rw [hj]
  norm_num
  ring

lemma fermion_pair_phase_envelope_s2_upper_bound_j1 (y : ℝ) (hy1 : 16 / 15 ≤ y) (hy2 : y < 256 / 15) :
    dyadic_phase_envelope.S 2 y = y / 4 + 16 / 15 := by
  dsimp [dyadic_phase_envelope.S]
  have hlog16 : 0 < Real.log 16 := Real.log_pos (by norm_num)
  have hpos : 0 < y * 15 := by linarith
  have h1 : 1 ≤ Real.log (y * 15) / Real.log 16 := by
    rw [le_div_iff₀ hlog16, one_mul]
    have : (16 : ℝ) ≤ y * 15 := by linarith
    exact Real.log_le_log (by norm_num) this
  have h2 : Real.log (y * 15) / Real.log 16 < 2 := by
    rw [div_lt_iff₀ hlog16]
    have : y * 15 < 16 ^ 2 := by linarith
    have hlog_sq : 2 * Real.log 16 = Real.log (16 ^ 2) := by
      rw [← Real.log_rpow (by norm_num : (0 : ℝ) < 16)]
      norm_num
    rw [hlog_sq]
    exact Real.log_lt_log hpos this
  have hcalc1 : ((2 : ℝ) ^ 2) ^ 2 - 1 = 15 := by norm_num
  have hcalc2 : ((2 : ℝ) ^ 2) ^ 2 = 16 := by norm_num
  have hj : ⌊Real.log (y * (((2 : ℝ) ^ 2) ^ 2 - 1)) / Real.log (((2 : ℝ) ^ 2) ^ 2)⌋ = (1 : ℤ) := by
    rw [hcalc1, hcalc2]
    rw [Int.floor_eq_iff]
    push_cast
    exact ⟨h1, by linarith⟩
  rw [hj]
  norm_num
  ring

lemma fermion_pair_phase_envelope_s2_upper_bound_sq_div_le (y : ℝ) (hy1 : 1 / 4 ≤ y) (hy2 : y ≤ 16) :
    (dyadic_phase_envelope.S 2 y) ^ 2 / y ≤ 27 / 10 := by
  rcases lt_or_ge y (16 / 15) with hlt | hge
  · rw [fermion_pair_phase_envelope_s2_upper_bound_j0 y (by linarith) hlt]
    have hpos : 0 < y := by linarith
    rw [div_le_iff₀ hpos]
    have hprod : (30 * y - 1) * (15 * y - 32) ≤ 0 := by
      have h1 : 0 ≤ 30 * y - 1 := by linarith
      have h2 : 15 * y - 32 ≤ 0 := by linarith
      nlinarith
    linarith
  · rw [fermion_pair_phase_envelope_s2_upper_bound_j1 y hge (by linarith)]
    have hpos : 0 < y := by linarith
    rw [div_le_iff₀ hpos]
    have hprod : (15 * y - 8) * (15 * y - 512) ≤ 0 := by
      have h1 : 0 ≤ 15 * y - 8 := by linarith
      have h2 : 15 * y - 512 ≤ 0 := by linarith
      nlinarith
    linarith

lemma fermion_pair_phase_envelope_s2_upper_bound_k0 (t : ℝ) (ht : 1 ≤ t ∧ t ≤ 2) :
    let A : ℝ := (2 : ℝ) ^ 2
    let x : ℝ := (2 : ℝ) ^ 0 * t
    let sx : ℝ := dyadic_phase_envelope.S 2 x
    let sxa : ℝ := dyadic_phase_envelope.S 2 (x / A)
    max (sx ^ 2 / x) (max (A * sxa ^ 2 / x) ((sx + Real.sqrt A * sxa) ^ 2 / (2 * x))) ≤ 27 / 10 := by
  intro A x sx sxa
  have hA_val : A = 4 := by norm_num [A]
  have hsqrtA : Real.sqrt A = 2 := by
    rw [hA_val, show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hx_val : x = t := by
    change (2 : ℝ) ^ 0 * t = t
    norm_num
  have hxA_val : x / A = t / 4 := by
    rw [hx_val, hA_val]
  rw [max_le_iff, max_le_iff]
  refine ⟨?_, ?_, ?_⟩
  · have hx1 : 1 / 4 ≤ x := by rw [hx_val]; linarith [ht.1]
    have hx2 : x ≤ 16 := by rw [hx_val]; linarith [ht.2]
    exact fermion_pair_phase_envelope_s2_upper_bound_sq_div_le x hx1 hx2
  · have : A * sxa ^ 2 / x = sxa ^ 2 / (x / A) := by rw [hA_val]; ring
    rw [this]
    have hy1 : 1 / 4 ≤ x / A := by rw [hxA_val]; linarith [ht.1]
    have hy2 : x / A ≤ 16 := by rw [hxA_val]; linarith [ht.2]
    exact fermion_pair_phase_envelope_s2_upper_bound_sq_div_le (x / A) hy1 hy2
  · have hsxa : sxa = t / 4 + 4 / 15 := by
      change dyadic_phase_envelope.S 2 (x / A) = t / 4 + 4 / 15
      rw [hxA_val]
      exact fermion_pair_phase_envelope_s2_upper_bound_j0 (t / 4) (by linarith [ht.1]) (by linarith [ht.2])
    rw [hsxa, hsqrtA, hx_val]
    rcases lt_or_ge t (16 / 15) with hlt | hge
    · have hsx : sx = t + 4 / 15 := by
        change dyadic_phase_envelope.S 2 x = t + 4 / 15
        rw [hx_val]
        exact fermion_pair_phase_envelope_s2_upper_bound_j0 t (by linarith [ht.1]) hlt
      rw [hsx]
      have hpos : 0 < 2 * t := by linarith [ht.1]
      rw [div_le_iff₀ hpos]
      have hprod : (15 * t - 16) * (15 * t - 4) ≤ 0 := by
        have h1 : 15 * t - 16 ≤ 0 := by linarith
        have h2 : 0 ≤ 15 * t - 4 := by linarith
        nlinarith
      linarith
    · have hsx : sx = t / 4 + 16 / 15 := by
        change dyadic_phase_envelope.S 2 x = t / 4 + 16 / 15
        rw [hx_val]
        exact fermion_pair_phase_envelope_s2_upper_bound_j1 t hge (by linarith [ht.2])
      rw [hsx]
      have hpos : 0 < 2 * t := by linarith [ht.1]
      rw [div_le_iff₀ hpos]
      have hprod : (15 * t - 16) * (15 * t - 64) ≤ 0 := by
        have h1 : 0 ≤ 15 * t - 16 := by linarith
        have h2 : 15 * t - 64 ≤ 0 := by linarith
        nlinarith
      linarith

lemma fermion_pair_phase_envelope_s2_upper_bound_k1 (t : ℝ) (ht : 1 ≤ t ∧ t ≤ 2) :
    let A : ℝ := (2 : ℝ) ^ 2
    let x : ℝ := (2 : ℝ) ^ 1 * t
    let sx : ℝ := dyadic_phase_envelope.S 2 x
    let sxa : ℝ := dyadic_phase_envelope.S 2 (x / A)
    max (sx ^ 2 / x) (max (A * sxa ^ 2 / x) ((sx + Real.sqrt A * sxa) ^ 2 / (2 * x))) ≤ 27 / 10 := by
  intro A x sx sxa
  have hA_val : A = 4 := by norm_num [A]
  have hsqrtA : Real.sqrt A = 2 := by
    rw [hA_val, show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hx_val : x = 2 * t := by
    change (2 : ℝ) ^ 1 * t = 2 * t
    norm_num
  have hxA_val : x / A = t / 2 := by
    rw [hx_val, hA_val]
    ring
  rw [max_le_iff, max_le_iff]
  refine ⟨?_, ?_, ?_⟩
  · have hx1 : 1 / 4 ≤ x := by rw [hx_val]; linarith [ht.1]
    have hx2 : x ≤ 16 := by rw [hx_val]; linarith [ht.2]
    exact fermion_pair_phase_envelope_s2_upper_bound_sq_div_le x hx1 hx2
  · have : A * sxa ^ 2 / x = sxa ^ 2 / (x / A) := by rw [hA_val]; ring
    rw [this]
    have hy1 : 1 / 4 ≤ x / A := by rw [hxA_val]; linarith [ht.1]
    have hy2 : x / A ≤ 16 := by rw [hxA_val]; linarith [ht.2]
    exact fermion_pair_phase_envelope_s2_upper_bound_sq_div_le (x / A) hy1 hy2
  · have hsxa : sxa = t / 2 + 4 / 15 := by
      change dyadic_phase_envelope.S 2 (x / A) = t / 2 + 4 / 15
      rw [hxA_val]
      exact fermion_pair_phase_envelope_s2_upper_bound_j0 (t / 2) (by linarith [ht.1]) (by linarith [ht.2])
    have hsx : sx = t / 2 + 16 / 15 := by
      change dyadic_phase_envelope.S 2 x = t / 2 + 16 / 15
      rw [hx_val]
      have h1 : 16 / 15 ≤ 2 * t := by linarith [ht.1]
      have h2 : 2 * t < 256 / 15 := by linarith [ht.2]
      have this_eq := fermion_pair_phase_envelope_s2_upper_bound_j1 (2 * t) h1 h2
      rw [this_eq]
      ring
    rw [hsx, hsxa, hsqrtA, hx_val]
    have hpos : 0 < 2 * (2 * t) := by linarith [ht.1]
    rw [div_le_iff₀ hpos]
    have hprod : (15 * t - 8) * (15 * t - 32) ≤ 0 := by
      have h1 : 0 ≤ 15 * t - 8 := by linarith [ht.1]
      have h2 : 15 * t - 32 ≤ 0 := by linarith [ht.2]
      nlinarith
    linarith

lemma fermion_pair_phase_envelope_s2_upper_bound_k2 (t : ℝ) (ht : 1 ≤ t ∧ t ≤ 2) :
    let A : ℝ := (2 : ℝ) ^ 2
    let x : ℝ := (2 : ℝ) ^ 2 * t
    let sx : ℝ := dyadic_phase_envelope.S 2 x
    let sxa : ℝ := dyadic_phase_envelope.S 2 (x / A)
    max (sx ^ 2 / x) (max (A * sxa ^ 2 / x) ((sx + Real.sqrt A * sxa) ^ 2 / (2 * x))) ≤ 27 / 10 := by
  intro A x sx sxa
  have hA_val : A = 4 := by norm_num [A]
  have hsqrtA : Real.sqrt A = 2 := by
    rw [hA_val, show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hx_val : x = 4 * t := by
    change (2 : ℝ) ^ 2 * t = 4 * t
    norm_num
  have hxA_val : x / A = t := by
    rw [hx_val, hA_val]
    ring
  rw [max_le_iff, max_le_iff]
  refine ⟨?_, ?_, ?_⟩
  · have hx1 : 1 / 4 ≤ x := by rw [hx_val]; linarith [ht.1]
    have hx2 : x ≤ 16 := by rw [hx_val]; linarith [ht.2]
    exact fermion_pair_phase_envelope_s2_upper_bound_sq_div_le x hx1 hx2
  · have : A * sxa ^ 2 / x = sxa ^ 2 / (x / A) := by rw [hA_val]; ring
    rw [this]
    have hy1 : 1 / 4 ≤ x / A := by rw [hxA_val]; linarith [ht.1]
    have hy2 : x / A ≤ 16 := by rw [hxA_val]; linarith [ht.2]
    exact fermion_pair_phase_envelope_s2_upper_bound_sq_div_le (x / A) hy1 hy2
  · have hsx : sx = t + 16 / 15 := by
      change dyadic_phase_envelope.S 2 x = t + 16 / 15
      rw [hx_val]
      have h1 : 16 / 15 ≤ 4 * t := by linarith [ht.1]
      have h2 : 4 * t < 256 / 15 := by linarith [ht.2]
      have this_eq := fermion_pair_phase_envelope_s2_upper_bound_j1 (4 * t) h1 h2
      rw [this_eq]
      ring
    rw [hsx, hsqrtA, hx_val]
    rcases lt_or_ge t (16 / 15) with hlt | hge
    · have hsxa : sxa = t + 4 / 15 := by
        change dyadic_phase_envelope.S 2 (x / A) = t + 4 / 15
        rw [hxA_val]
        exact fermion_pair_phase_envelope_s2_upper_bound_j0 t (by linarith [ht.1]) hlt
      rw [hsxa]
      have hpos : 0 < 2 * (4 * t) := by linarith [ht.1]
      rw [div_le_iff₀ hpos]
      have hprod : (15 * t - 16) * (15 * t - 4) ≤ 0 := by
        have h1 : 15 * t - 16 ≤ 0 := by linarith
        have h2 : 0 ≤ 15 * t - 4 := by linarith
        nlinarith
      linarith
    · have hsxa : sxa = t / 4 + 16 / 15 := by
        change dyadic_phase_envelope.S 2 (x / A) = t / 4 + 16 / 15
        rw [hxA_val]
        exact fermion_pair_phase_envelope_s2_upper_bound_j1 t hge (by linarith [ht.2])
      rw [hsxa]
      have hpos : 0 < 2 * (4 * t) := by linarith [ht.1]
      rw [div_le_iff₀ hpos]
      have hprod : (15 * t - 16) * (15 * t - 64) ≤ 0 := by
        have h1 : 0 ≤ 15 * t - 16 := by linarith
        have h2 : 15 * t - 64 ≤ 0 := by linarith
        nlinarith
      linarith

lemma fermion_pair_phase_envelope_s2_upper_bound_k3 (t : ℝ) (ht : 1 ≤ t ∧ t ≤ 2) :
    let A : ℝ := (2 : ℝ) ^ 2
    let x : ℝ := (2 : ℝ) ^ 3 * t
    let sx : ℝ := dyadic_phase_envelope.S 2 x
    let sxa : ℝ := dyadic_phase_envelope.S 2 (x / A)
    max (sx ^ 2 / x) (max (A * sxa ^ 2 / x) ((sx + Real.sqrt A * sxa) ^ 2 / (2 * x))) ≤ 27 / 10 := by
  intro A x sx sxa
  have hA_val : A = 4 := by norm_num [A]
  have hsqrtA : Real.sqrt A = 2 := by
    rw [hA_val, show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hx_val : x = 8 * t := by
    change (2 : ℝ) ^ 3 * t = 8 * t
    norm_num
  have hxA_val : x / A = 2 * t := by
    rw [hx_val, hA_val]
    ring
  rw [max_le_iff, max_le_iff]
  refine ⟨?_, ?_, ?_⟩
  · have hx1 : 1 / 4 ≤ x := by rw [hx_val]; linarith [ht.1]
    have hx2 : x ≤ 16 := by rw [hx_val]; linarith [ht.2]
    exact fermion_pair_phase_envelope_s2_upper_bound_sq_div_le x hx1 hx2
  · have : A * sxa ^ 2 / x = sxa ^ 2 / (x / A) := by rw [hA_val]; ring
    rw [this]
    have hy1 : 1 / 4 ≤ x / A := by rw [hxA_val]; linarith [ht.1]
    have hy2 : x / A ≤ 16 := by rw [hxA_val]; linarith [ht.2]
    exact fermion_pair_phase_envelope_s2_upper_bound_sq_div_le (x / A) hy1 hy2
  · have hsxa : sxa = t / 2 + 16 / 15 := by
      change dyadic_phase_envelope.S 2 (x / A) = t / 2 + 16 / 15
      rw [hxA_val]
      have h1 : 16 / 15 ≤ 2 * t := by linarith [ht.1]
      have h2 : 2 * t < 256 / 15 := by linarith [ht.2]
      have this_eq := fermion_pair_phase_envelope_s2_upper_bound_j1 (2 * t) h1 h2
      rw [this_eq]
      ring
    have hsx : sx = 2 * t + 16 / 15 := by
      change dyadic_phase_envelope.S 2 x = 2 * t + 16 / 15
      rw [hx_val]
      have h1 : 16 / 15 ≤ 8 * t := by linarith [ht.1]
      have h2 : 8 * t < 256 / 15 := by linarith [ht.2]
      have this_eq := fermion_pair_phase_envelope_s2_upper_bound_j1 (8 * t) h1 h2
      rw [this_eq]
      ring
    rw [hsx, hsxa, hsqrtA, hx_val]
    have hpos : 0 < 2 * (8 * t) := by linarith [ht.1]
    rw [div_le_iff₀ hpos]
    have hprod : (15 * t - 8) * (15 * t - 32) ≤ 0 := by
      have h1 : 0 ≤ 15 * t - 8 := by linarith [ht.1]
      have h2 : 15 * t - 32 ≤ 0 := by linarith [ht.2]
      nlinarith
    linarith

lemma fermion_pair_phase_envelope_s2_upper_bound_envelope_le (t : ℝ) (ht : 1 ≤ t ∧ t ≤ 2) :
    dyadic_phase_envelope 2 t ≤ 27 / 10 := by
  change (Finset.range 4).fold max 0 (fun k =>
    let A : ℝ := (2 : ℝ) ^ 2
    let x : ℝ := (2 : ℝ) ^ k * t
    let sx : ℝ := dyadic_phase_envelope.S 2 x
    let sxa : ℝ := dyadic_phase_envelope.S 2 (x / A)
    max (sx ^ 2 / x) (max (A * sxa ^ 2 / x) ((sx + Real.sqrt A * sxa) ^ 2 / (2 * x)))) ≤ 27 / 10
  rw [Finset.fold_max_le]
  refine ⟨by norm_num, ?_⟩
  intro k hk
  rw [Finset.mem_range] at hk
  interval_cases k
  · exact fermion_pair_phase_envelope_s2_upper_bound_k0 t ht
  · exact fermion_pair_phase_envelope_s2_upper_bound_k1 t ht
  · exact fermion_pair_phase_envelope_s2_upper_bound_k2 t ht
  · exact fermion_pair_phase_envelope_s2_upper_bound_k3 t ht

/-- Upper bound of the dyadic phase envelope at s = 2 on the interval [1, 2]. -/
theorem fermion_pair_phase_envelope_s2_upper_bound (t : ℝ) (ht : 1 ≤ t ∧ t ≤ 2) :
    let p : ℝ := (1 : ℝ) / 5
    let q : ℝ := (4 : ℝ) / 5
    dyadic_phase_envelope 2 t / Real.sqrt (2 * Real.pi * p * q) ≤ 27 / (4 * Real.sqrt (2 * Real.pi)) := by
  intro p q
  dsimp [p, q]
  have hE : dyadic_phase_envelope 2 t ≤ 27 / 10 :=
    fermion_pair_phase_envelope_s2_upper_bound_envelope_le t ht
  have hpi : 0 < Real.pi := Real.pi_pos
  have h2pi : 0 < 2 * Real.pi := by linarith
  have hsq : Real.sqrt (2 * Real.pi * (1 / 5) * (4 / 5)) = (2 / 5) * Real.sqrt (2 * Real.pi) := by
    have h1 : 2 * Real.pi * (1 / 5) * (4 / 5) = (2 / 5) ^ 2 * (2 * Real.pi) := by ring
    rw [h1, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  rw [hsq]
  have hsqrt_pos : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr h2pi
  have h_lhs : dyadic_phase_envelope 2 t / (2 / 5 * Real.sqrt (2 * Real.pi)) =
      (dyadic_phase_envelope 2 t / (2 / 5)) / Real.sqrt (2 * Real.pi) := by
    rw [div_div, mul_comm]
  have h_rhs : 27 / (4 * Real.sqrt (2 * Real.pi)) = (27 / 4) / Real.sqrt (2 * Real.pi) := by
    rw [div_div, mul_comm]
  rw [h_lhs, h_rhs]
  rw [div_le_div_iff_of_pos_right hsqrt_pos]
  linarith
