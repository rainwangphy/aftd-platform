import AFTD.Prelude
import AFTD.Kb.Tcs.Op869IntegerFoldScheduleConditional
import AFTD.Kb.Tcs.Op869LogIntegerBudgetUpper
import AFTD.Kb.Tcs.Op869BoundedAdversaryForces

/-!
# op869_fold_simulation_implies_forcing_growth

Topic: online_algorithms   Node: 83587051cb50

Provenance: helper lemma. Integer schedule and size estimate related to arXiv:2610.41516 Section 2.3.

For a positive simulation constant C, the fold simulation implies a bounded one-fold game forcing m^m colors on at most exp((3+2C)m³ log m) vertices for every m≥2.
-/

/-- The fold simulation implies the integer forcing-growth hypothesis. -/
theorem op869_fold_simulation_implies_forcing_growth (C : ℕ) (hC : 1 ≤ C)
    (hsim : ∀ n q t K D : ℕ, 1 ≤ t → t ≤ q → q ≤ K → 1 ≤ D →
      op869_bounded_adversary_forces 3 q K D n 0 (fun _ : Fin n => ∅) (fun _ : Fin n => ∅) →
      ∀ n' D' : ℕ,
      C * K^2 * q * n * D * 2^(C * ((q + t - 1) / t)) ≤ n' →
      C * K^2 * q * D * 2^(C * ((q + t - 1) / t)) ≤ D' →
      op869_bounded_adversary_forces 3 t K D' n' 0 (fun _ : Fin n' => ∅) (fun _ : Fin n' => ∅)) :
    ∃ C' : ℕ, 1 ≤ C' ∧ ∀ m : ℕ, 2 ≤ m → ∃ n D : ℕ,
      (n : ℝ) ≤ Real.exp ((C' : ℝ) * (m : ℝ)^3 * Real.log (m : ℝ)) ∧
      op869_bounded_adversary_forces 3 1 (m^m) D n 0 (fun _ : Fin n => ∅) (fun _ : Fin n => ∅) := by
  refine ⟨3+2*C, by omega, ?_⟩
  intro m hm
  let K := m^m
  let F := C*K^3*2^(C*(m+1))
  let n := F^(m^2)
  have hC0 : 0 < C := by omega
  have hm0 : 0 < m := by omega
  have hn0 : 0 < (n : ℝ) := by dsimp [n,F,K]; positivity
  have hlog := op869_log_integer_budget_upper C m hC hm
  change Real.log (n : ℝ) ≤ (3+2*(C : ℝ))*(m : ℝ)^3*Real.log (m : ℝ) at hlog
  refine ⟨n, F^m, ?_, ?_⟩
  · calc
      (n : ℝ) = Real.exp (Real.log (n : ℝ)) := (Real.exp_log hn0).symm
      _ ≤ Real.exp (((3+2*C : ℕ) : ℝ)*(m : ℝ)^3*Real.log (m : ℝ)) := by
        apply Real.exp_le_exp.mpr
        simpa using hlog
  · exact op869_integer_fold_schedule_conditional C m hC hm hsim n (le_refl n)
