import AFTD.Prelude
import AFTD.Kb.Tcs.Op869BoundedAdversaryForces
import AFTD.Kb.Tcs.Op869BoundedAdversaryForcesPad
import AFTD.Kb.Tcs.Op869BoundedAdversaryForcesSound
import AFTD.Kb.Tcs.Op869IntegerScheduleAsymptotic
import AFTD.Kb.Tcs.Op869GeneralBudgetInversion
import AFTD.Kb.Tcs.Op869LogIntegerBudgetLower
import AFTD.Kb.Tcs.Op869BoundedInitialVertexMono
import AFTD.Kb.Tcs.Op869BoundedAdversaryForcesUnbounded
import AFTD.Kb.Tcs.Op869AdversaryForcesSound
import AFTD.Kb.Tcs.Op869AdversaryForces
import AFTD.Kb.Tcs.ProperlyColorsKColorable
import AFTD.Kb.Tcs.Op869GraphFromPredecessors
import AFTD.Kb.Tcs.ColorsUsed
import AFTD.Kb.Tcs.IsOnlineColoringAlg

/-!
# op869_three_colorable_lower_bound_of_forcing

Topic: online_algorithms   Node: 91796867bb9c

Provenance: helper lemma. step towards op869_online_coloring_deterministic_lower_bound

If the bounded adversary game forces m^m colours on at most exp(C m³ log m) vertices for every m ≥ 2, then the three-colourable deterministic online colouring lower bound (exponents 1/3 and 2/3) holds.
-/

/-- Analytic assembly: growth of forceable colours in the bounded game on subexponential vertex budgets yields the three-colourable deterministic online lower bound. -/
theorem op869_three_colorable_lower_bound_of_forcing
    (hgr : ∃ C : ℕ, 1 ≤ C ∧ ∀ m : ℕ, 2 ≤ m → ∃ n D : ℕ,
      (n : ℝ) ≤ Real.exp ((C : ℝ) * (m : ℝ) ^ 3 * Real.log (m : ℝ)) ∧
      op869_bounded_adversary_forces 3 1 (m ^ m) D n 0 (fun _ : Fin n => ∅) (fun _ : Fin n => ∅)) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ A : SimpleGraph (Fin n) → (Fin n → ℕ),
        IsOnlineColoringAlg A → ProperlyColorsKColorable 3 A →
          ∃ G : SimpleGraph (Fin n), G.Colorable 3 ∧
            Real.exp (c * (Real.log (n : ℝ) ^ ((1 : ℝ) / 3)) *
              (Real.log (Real.log (n : ℝ)) ^ ((2 : ℝ) / 3))) ≤ (colorsUsed (A G) : ℝ) := by
  obtain ⟨C, hC, hgr⟩ := hgr
  let budget : ℕ → ℕ := fun m => (op869_asym_integer_budget_internal 1 m)^C
  let D : ℝ := 80*(C : ℝ)
  have hCr : (1 : ℝ) ≤ C := by exact_mod_cast hC
  have hC0 : 0 < C := by omega
  have hD : 1 ≤ D := by dsimp [D]; nlinarith
  have hbig : ∀ m, 1 ≤ m → m ≤ budget m := by
    intro m hm
    have hbase := op869_asym_budget_big_internal 1 m (by decide) hm
    have hpow : op869_asym_integer_budget_internal 1 m ≤ (op869_asym_integer_budget_internal 1 m)^C := Nat.le_pow hC0
    exact le_trans hbase hpow
  have hsucc : ∀ m, 2 ≤ m → Real.log (budget (m+1) : ℝ) ≤ D*(m : ℝ)^3*Real.log (m : ℝ) := by
    intro m hm
    have hh : Real.log (op869_asym_integer_budget_internal 1 (m+1) : ℝ) ≤
        80*(m : ℝ)^3*Real.log (m : ℝ) := by
      have h := op869_asym_log_succ_internal 1 m (by decide) hm
      norm_num [op869_asym_integer_budget_internal] at h ⊢
      exact h
    have hh' := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ (C : ℝ))
    have hlog : Real.log (budget (m+1) : ℝ) =
        (C : ℝ) * Real.log (op869_asym_integer_budget_internal 1 (m+1) : ℝ) := by
      dsimp [budget]
      push_cast
      rw [Real.log_pow]
    rw [hlog]
    dsimp [D]
    nlinarith
  obtain ⟨c, hc, n₀, hasym⟩ := op869_general_budget_inversion budget D hD hbig hsucc
  refine ⟨c, hc, n₀, ?_⟩
  intro n hn A hA hproper
  obtain ⟨m, hm, hbudget, hbound⟩ := hasym n hn
  obtain ⟨N, D', hsize, hwin⟩ := hgr m hm
  have hm0 : 0 < m := by omega
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlogm : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by linarith)
  have hmlog : 0 ≤ (m : ℝ)^3*Real.log (m : ℝ) := mul_nonneg (by positivity) hlogm
  have hlower : 3*(m : ℝ)^3*Real.log (m : ℝ) ≤ Real.log (op869_asym_integer_budget_internal 1 m : ℝ) := by
    simpa [op869_asym_integer_budget_internal] using op869_log_integer_budget_lower 1 m (by decide) hm
  have hsimple : (m : ℝ)^3*Real.log (m : ℝ) ≤ Real.log (op869_asym_integer_budget_internal 1 m : ℝ) := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hsimple (by positivity : 0 ≤ (C : ℝ))
  have hlogB : Real.log (budget m : ℝ) = (C : ℝ)*Real.log (op869_asym_integer_budget_internal 1 m : ℝ) := by
    dsimp [budget]
    push_cast
    rw [Real.log_pow]
  have hBpos : 0 < (budget m : ℝ) := by
    have hb : 1 ≤ budget m := le_trans (by omega : 1 ≤ m) (hbig m (by omega))
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) hb)
  have hexp : Real.exp ((C : ℝ)*(m : ℝ)^3*Real.log (m : ℝ)) ≤ (budget m : ℝ) := by
    calc
      Real.exp ((C : ℝ)*(m : ℝ)^3*Real.log (m : ℝ)) ≤ Real.exp (Real.log (budget m : ℝ)) := by
        apply Real.exp_le_exp.mpr
        rw [hlogB]
        nlinarith
      _ = (budget m : ℝ) := Real.exp_log hBpos
  have hbudgetr : (budget m : ℝ) ≤ n := by exact_mod_cast hbudget
  have hNr : (N : ℝ) ≤ n := le_trans hsize (le_trans hexp hbudgetr)
  have hNn : N ≤ n := by exact_mod_cast hNr
  have hpad := op869_bounded_initial_vertex_mono hNn 3 1 (m^m) D' (by decide) hwin
  have hplay := op869_bounded_adversary_forces_unbounded 3 1 (m^m) D' n 0
    (fun _ : Fin n => ∅) (fun _ : Fin n => ∅) hpad
  obtain ⟨G, hcolor, hused⟩ := op869_adversary_forces_sound 3 (m^m) A hA hproper n 0
    (fun _ : Fin n => ∅) (fun _ : Fin n => ∅) hplay (by intro a ha; omega)
  refine ⟨G, hcolor, le_trans hbound ?_⟩
  exact_mod_cast hused
