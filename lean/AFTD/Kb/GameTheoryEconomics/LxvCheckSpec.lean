import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LxvEf1
import AFTD.Kb.GameTheoryEconomics.LxvProfile
import AFTD.Kb.GameTheoryEconomics.LxvOpt
import AFTD.Kb.GameTheoryEconomics.LxvCheck
import AFTD.Kb.GameTheoryEconomics.LxvCheckEqTrue

/-!
# lxv_check_spec

Topic: fair_division   Node: aac2cb8822e4

Unpacked finite check: lxv_opt is EF1, no EF1 allocation is strictly leximin-better, and every EF1 allocation not strictly leximin-worse than lxv_opt is lxv_opt.
-/

lemma lxv_check_spec : lxv_ef1 lxv_opt = true ∧ ∀ τ : Fin 6 → Fin 4, lxv_ef1 τ = true →
    ¬ List.Lex (· < ·) (lxv_profile lxv_opt) (lxv_profile τ) ∧
      (List.Lex (· < ·) (lxv_profile τ) (lxv_profile lxv_opt) ∨ τ = lxv_opt) := by
  have h := lxv_check_eq_true
  simp only [lxv_check, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq] at h
  refine ⟨h.1, fun τ hτ => ?_⟩
  have hτ' : (![τ 0, τ 1, τ 2, τ 3, τ 4, τ 5] : Fin 6 → Fin 4) = τ := by
    ext g; fin_cases g <;> rfl
  have := h.2 (τ 0) (τ 1) (τ 2) (τ 3) (τ 4) (τ 5)
  rw [hτ'] at this
  rcases this with h1 | ⟨h1, h2⟩
  · rw [hτ] at h1; exact absurd h1 (by simp)
  · refine ⟨h1, h2.imp id fun h3 => funext fun g => ?_⟩
    simpa using h3 g
