import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# arrangement3_diophantine_system

Topic: combinatorics   Node: d1f99b7f7f9f

Provenance: helper lemma. arXiv:2610.38386, Proposition 5.1 proof

For integers $\kappa, a', c', \xi', \eta'$ satisfying $\xi' + \eta' = \kappa$, $4\kappa^2 + 3(a'^2 + c'^2) + \xi'^2 + \eta'^2 = 30$, and corner non-degeneracy $a' \neq 0$, $c' \neq 0$, $a'^2 \neq c'^2$, necessarily $\kappa = 0$, $\xi' = 0$, and $\eta' = 0$.
-/

private lemma arrangement3_diophantine_system_sq_add_sq_ge_five (a c : ℤ)
    (ha : a ≠ 0) (hc : c ≠ 0) (hac : a^2 ≠ c^2) : 5 ≤ a^2 + c^2 := by
  have ha2 : 0 < a^2 := sq_pos_of_ne_zero ha
  have hc2 : 0 < c^2 := sq_pos_of_ne_zero hc
  by_contra h
  push Not at h
  have ha_lt : a^2 < 5 := by nlinarith
  have hc_lt : c^2 < 5 := by nlinarith
  have ha_lo : -2 ≤ a := by
    by_contra hh
    have h3 : a ≤ -3 := by omega
    nlinarith [sq_nonneg (a + 3)]
  have ha_hi : a ≤ 2 := by
    by_contra hh
    have h3 : 3 ≤ a := by omega
    nlinarith [sq_nonneg (a - 3)]
  have hc_lo : -2 ≤ c := by
    by_contra hh
    have h3 : c ≤ -3 := by omega
    nlinarith [sq_nonneg (c + 3)]
  have hc_hi : c ≤ 2 := by
    by_contra hh
    have h3 : 3 ≤ c := by omega
    nlinarith [sq_nonneg (c - 3)]
  interval_cases a <;> interval_cases c <;> norm_num at *

private lemma arrangement3_diophantine_system_sq_add_sq_ne_seven (a c : ℤ) :
    a^2 + c^2 ≠ 7 := by
  intro h
  have ha_lt : a^2 < 9 := by nlinarith [sq_nonneg c]
  have hc_lt : c^2 < 9 := by nlinarith [sq_nonneg a]
  have ha_lo : -2 ≤ a := by
    by_contra hh
    have h3 : a ≤ -3 := by omega
    nlinarith [sq_nonneg (a + 3)]
  have ha_hi : a ≤ 2 := by
    by_contra hh
    have h3 : 3 ≤ a := by omega
    nlinarith [sq_nonneg (a - 3)]
  have hc_lo : -2 ≤ c := by
    by_contra hh
    have h3 : c ≤ -3 := by omega
    nlinarith [sq_nonneg (c + 3)]
  have hc_hi : c ≤ 2 := by
    by_contra hh
    have h3 : 3 ≤ c := by omega
    nlinarith [sq_nonneg (c - 3)]
  interval_cases a <;> interval_cases c <;> norm_num at h

private lemma arrangement3_diophantine_system_sq_add_sq_ne_four_of_ne_zero (a c : ℤ)
    (ha : a ≠ 0) (hc : c ≠ 0) :
    a^2 + c^2 ≠ 4 := by
  intro h
  have ha_lt : a^2 < 9 := by nlinarith [sq_nonneg c]
  have hc_lt : c^2 < 9 := by nlinarith [sq_nonneg a]
  have ha_lo : -2 ≤ a := by
    by_contra hh
    have h3 : a ≤ -3 := by omega
    nlinarith [sq_nonneg (a + 3)]
  have ha_hi : a ≤ 2 := by
    by_contra hh
    have h3 : 3 ≤ a := by omega
    nlinarith [sq_nonneg (a - 3)]
  have hc_lo : -2 ≤ c := by
    by_contra hh
    have h3 : c ≤ -3 := by omega
    nlinarith [sq_nonneg (c + 3)]
  have hc_hi : c ≤ 2 := by
    by_contra hh
    have h3 : 3 ≤ c := by omega
    nlinarith [sq_nonneg (c - 3)]
  interval_cases a <;> interval_cases c <;> norm_num at h
  all_goals omega

/-- Diophantine constraint from the sum of squares identity in the proof of Proposition 5.1. -/
lemma arrangement3_diophantine_system (κ a' c' ξ' η' : ℤ)
    (h_sum : ξ' + η' = κ)
    (h_eq : 4 * κ^2 + 3 * (a'^2 + c'^2) + ξ'^2 + η'^2 = 30)
    (h_corners : a' ≠ 0 ∧ c' ≠ 0 ∧ a'^2 ≠ c'^2) :
    κ = 0 ∧ ξ' = 0 ∧ η' = 0 := by
  obtain ⟨ha, hc, hac⟩ := h_corners
  have hη : η' = κ - ξ' := by omega
  subst η'
  have hS : 5 ≤ a'^2 + c'^2 :=
    arrangement3_diophantine_system_sq_add_sq_ge_five a' c' ha hc hac
  have hNot7 : a'^2 + c'^2 ≠ 7 :=
    arrangement3_diophantine_system_sq_add_sq_ne_seven a' c'
  have hNot4 : a'^2 + c'^2 ≠ 4 :=
    arrangement3_diophantine_system_sq_add_sq_ne_four_of_ne_zero a' c' ha hc
  have hκ_lt : κ^2 < 4 := by
    nlinarith [hS, sq_nonneg ξ', sq_nonneg (κ - ξ')]
  have hκ_lo : -1 ≤ κ := by
    by_contra hh
    have h3 : κ ≤ -2 := by omega
    nlinarith [sq_nonneg (κ + 2)]
  have hκ_hi : κ ≤ 1 := by
    by_contra hh
    have h3 : 2 ≤ κ := by omega
    nlinarith [sq_nonneg (κ - 2)]
  have hξ_sq : ξ'^2 ≤ 15 := by
    nlinarith [hS, sq_nonneg κ, sq_nonneg (κ - ξ')]
  have hξ_lo : -3 ≤ ξ' := by
    by_contra hh
    have h3 : ξ' ≤ -4 := by omega
    nlinarith [sq_nonneg (ξ' + 4)]
  have hξ_hi : ξ' ≤ 3 := by
    by_contra hh
    have h3 : 4 ≤ ξ' := by omega
    nlinarith [sq_nonneg (ξ' - 4)]
  interval_cases κ <;> interval_cases ξ' <;> norm_num at h_eq ⊢
  all_goals omega
