import AFTD.Prelude
import AFTD.Kb.Tcs.Op869IntegerScheduleAsymptotic

/-!
# op869_general_budget_inversion

Topic: online_algorithms   Node: 100104c9acc5

Provenance: helper lemma. General form of the logarithmic inversion used in arXiv:2610.41516 Section 2.3.

For any integer budget growing at least linearly whose next-budget logarithm is O(m³ log m), every sufficiently large n admits a feasible m with m^m at least exp(c(log n)^(1/3)(log log n)^(2/3)).
-/

/-- Invert any integer budget with the fold-schedule logarithmic growth bound. -/
theorem op869_general_budget_inversion (budget : ℕ → ℕ) (D : ℝ) (hD1 : 1 ≤ D)
    (hbig : ∀ m, 1 ≤ m → m ≤ budget m)
    (hsucc : ∀ m, 2 ≤ m → Real.log (budget (m+1) : ℝ) ≤ D*(m : ℝ)^3*Real.log (m : ℝ)) : ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∃ m : ℕ, 2 ≤ m ∧
      budget m ≤ n ∧
      Real.exp (c * (Real.log (n : ℝ) ^ ((1 : ℝ) / 3)) *
        (Real.log (Real.log (n : ℝ)) ^ ((2 : ℝ) / 3))) ≤ (m^m : ℝ) := by
  let E : ℝ := 4+D/Real.log 2
  let W : ℝ := D*E^2+1
  have hD0 : 0 ≤ D := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hE0 : 0 ≤ E := by
    dsimp [E]
    have h := div_nonneg hD0 hlog2.le
    linarith
  have hW0 : 0 < W := by
    dsimp [W]
    have h := mul_nonneg hD0 (sq_nonneg E)
    linarith
  refine ⟨1/W, by positivity, max 3 (budget 2), ?_⟩
  intro n hn
  have hn3 : 3 ≤ n := le_trans (le_max_left _ _) hn
  have hnB : budget 2 ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨m, hm, hbudget, hnext⟩ := op869_asym_maximal_budget_internal budget hbig n hnB
  refine ⟨m, hm, ?_, ?_⟩
  · exact hbudget
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hn3r : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
  have hx1 : 1 ≤ Real.log (n : ℝ) :=
    (Real.le_log_iff_exp_le hn0).2 (le_trans Real.exp_one_lt_three.le hn3r)
  have hx0 : 0 ≤ Real.log (n : ℝ) := by linarith
  have hy0 : 0 ≤ Real.log (Real.log (n : ℝ)) := Real.log_nonneg hx1
  have hm0 : 0 ≤ (m : ℝ) := by positivity
  have hm2r : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hl0 : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by linarith)
  have hcast : (n : ℝ) ≤ (budget (m+1) : ℕ) := by exact_mod_cast (Nat.le_of_lt hnext)
  have hlogn : Real.log (n : ℝ) ≤ Real.log (budget (m+1) : ℕ) :=
    Real.log_le_log hn0 hcast
  have hxbound : Real.log (n : ℝ) ≤ D*(m : ℝ)^3*Real.log (m : ℝ) := le_trans hlogn (hsucc m hm)
  have hybound : Real.log (Real.log (n : ℝ)) ≤ E*Real.log (m : ℝ) := by
    have h := op869_asym_loglog_internal (Real.log (n : ℝ)) (m : ℝ) D (by linarith) hm2r hD1 hxbound
    simpa [E] using h
  have hscalar := op869_asym_scalar_inv_internal (Real.log (n : ℝ)) (Real.log (Real.log (n : ℝ)))
    (m : ℝ) (Real.log (m : ℝ)) D E hx0 hy0 hm0 hl0 hD0 hE0 hxbound hybound
  have hscale : (1/W) * (Real.log (n : ℝ) ^ ((1 : ℝ)/3)) *
      (Real.log (Real.log (n : ℝ)) ^ ((2 : ℝ)/3)) ≤ (m : ℝ)*Real.log (m : ℝ) := by
    calc
      (1/W) * (Real.log (n : ℝ) ^ ((1 : ℝ)/3)) *
          (Real.log (Real.log (n : ℝ)) ^ ((2 : ℝ)/3)) =
          ((Real.log (n : ℝ) ^ ((1 : ℝ)/3)) *
          (Real.log (Real.log (n : ℝ)) ^ ((2 : ℝ)/3))) / W := by ring
      _ ≤ (m : ℝ)*Real.log (m : ℝ) := by
        apply (div_le_iff₀ hW0).2
        simpa only [W, mul_assoc, mul_comm, mul_left_comm] using hscalar
  calc
    Real.exp ((1/W) * (Real.log (n : ℝ) ^ ((1 : ℝ)/3)) *
        (Real.log (Real.log (n : ℝ)) ^ ((2 : ℝ)/3))) ≤
        Real.exp ((m : ℝ)*Real.log (m : ℝ)) := Real.exp_le_exp.mpr hscale
    _ = Real.exp (Real.log ((m : ℝ)^m)) := by rw [Real.log_pow]
    _ = (m^m : ℝ) := Real.exp_log (by positivity)
