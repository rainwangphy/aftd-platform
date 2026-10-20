import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiderBlockedOptionvals
import AFTD.Kb.GameTheoryEconomics.SpiderBlockedVal
import AFTD.Kb.GameTheoryEconomics.SpiderRho
import AFTD.Kb.GameTheoryEconomics.SpiderRhoStar
import AFTD.Kb.GameTheoryEconomics.SpiderLegEnd
import AFTD.Kb.GameTheoryEconomics.SpiderBlockedOptionvalsLe
import AFTD.Kb.GameTheoryEconomics.SpiderRhoZeroSame

/-!
# spider_blocked_optionvals_not_mem

Topic: combinatorial_games   Node: 1acd0913c2c8

Provenance: helper lemma. step towards spider_two_leg_blocked_incoming_val

For r ≥ 1 and β inward or outward, the closed-form value spider_blocked_val β r does not occur in the explicit options list of (in;{(r,β),(1,free)}).
-/

theorem spider_blocked_optionvals_not_mem_val_parity (delta : SpiderLegEnd) (m : ℕ) :
    spider_blocked_val delta m % 2 = (m + 1) % 2 := by
  dsimp [spider_blocked_val]
  split <;> split_ifs <;> omega

theorem spider_blocked_optionvals_not_mem_val_even (delta : SpiderLegEnd) (m : ℕ) (hm : m % 2 = 0) :
    spider_blocked_val delta m = m + 1 := by
  dsimp [spider_blocked_val]
  split <;> split_ifs <;> omega

theorem spider_blocked_optionvals_not_mem_cut_same_parity (r j : ℕ) (hj : 1 ≤ j) (hjr : j ≤ r) (beta : SpiderLegEnd)
    (hβ : beta = SpiderLegEnd.inward ∨ beta = SpiderLegEnd.outward) :
    (spider_rho (r - j) beta beta ^^^ spider_blocked_val beta (j - 1)) % 2 = r % 2 := by
  have h1 : spider_rho (r - j) beta beta = (r - j) % 2 := by
    rcases hβ with rfl | rfl <;> rfl
  have h2 : spider_blocked_val beta (j - 1) % 2 = j % 2 := by
    have := spider_blocked_optionvals_not_mem_val_parity beta (j - 1)
    omega
  rw [Nat.xor_mod_two_eq, h1]
  omega

theorem spider_blocked_optionvals_not_mem_cut_diff_inward (r j : ℕ) (hr : 2 ≤ r) (hr4 : r % 4 = 3)
    (hj : 1 ≤ j) (hj_lt : j ≤ r - 1) :
    spider_rho (r - j) SpiderLegEnd.outward SpiderLegEnd.inward ^^^
      spider_blocked_val SpiderLegEnd.outward (j - 1) ≠ r - 1 := by
  intro h
  let h_len := r - j
  have hrho_le : spider_rho h_len SpiderLegEnd.outward SpiderLegEnd.inward ≤ 1 := by
    dsimp [spider_rho]; split_ifs <;> omega
  have hval_le : spider_blocked_val SpiderLegEnd.outward (j - 1) ≤ (j - 1) + 1 :=
    spider_blocked_optionvals_le_val_le_succ _ _
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hrho_le with hrho0 | hrho1
  · rw [hrho0, zero_xor] at h
    have hj_eq : j - 1 = r - 2 := by omega
    rw [hj_eq] at h
    have hval : spider_blocked_val SpiderLegEnd.outward (r - 2) = r - 3 := by
      dsimp [spider_blocked_val]
      have : (r - 2) % 4 = 1 := by omega
      rw [if_pos this]
      omega
    omega
  · have h_even : Even (r - 1) := by
      rw [Nat.even_iff]
      omega
    have h_xor : 1 ^^^ (r - 1) = r := by
      rw [Nat.xor_comm, Nat.xor_one_of_even h_even]
      omega
    rw [hrho1] at h
    have h1 : spider_blocked_val SpiderLegEnd.outward (j - 1) = 1 ^^^ (r - 1) := by
      have := congr_arg (fun x => 1 ^^^ x) h
      rw [← Nat.xor_assoc, Nat.xor_self, zero_xor] at this
      exact this
    rw [h1, h_xor] at hval_le
    omega

theorem spider_blocked_optionvals_not_mem_cut_diff_outward (r j : ℕ) (hr : 2 ≤ r) (hr4 : r % 4 = 1)
    (hj : 1 ≤ j) (hj_lt : j ≤ r - 1) :
    spider_rho (r - j) SpiderLegEnd.inward SpiderLegEnd.outward ^^^
      spider_blocked_val SpiderLegEnd.inward (j - 1) ≠ r - 1 := by
  intro h
  let h_len := r - j
  have hrho_le : spider_rho h_len SpiderLegEnd.inward SpiderLegEnd.outward ≤ 1 := by
    dsimp [spider_rho]; split_ifs <;> omega
  have hval_le : spider_blocked_val SpiderLegEnd.inward (j - 1) ≤ (j - 1) + 1 :=
    spider_blocked_optionvals_le_val_le_succ _ _
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hrho_le with hrho0 | hrho1
  · rw [hrho0, zero_xor] at h
    have hj_eq : j - 1 = r - 2 := by omega
    rw [hj_eq] at h
    have hval : spider_blocked_val SpiderLegEnd.inward (r - 2) = r - 3 := by
      dsimp [spider_blocked_val]
      have : (r - 2) % 4 = 3 := by omega
      rw [if_pos this]
      omega
    omega
  · have h_even : Even (r - 1) := by
      rw [Nat.even_iff]
      omega
    have h_xor : 1 ^^^ (r - 1) = r := by
      rw [Nat.xor_comm, Nat.xor_one_of_even h_even]
      omega
    rw [hrho1] at h
    have h1 : spider_blocked_val SpiderLegEnd.inward (j - 1) = 1 ^^^ (r - 1) := by
      have := congr_arg (fun x => 1 ^^^ x) h
      rw [← Nat.xor_assoc, Nat.xor_self, zero_xor] at this
      exact this
    rw [h1, h_xor] at hval_le
    omega

/-- Non-membership: the closed-form value is never an actual option of the blocked two-leg family. -/
theorem spider_blocked_optionvals_not_mem (r : ℕ) (hr : 1 ≤ r) (beta : SpiderLegEnd)
    (hβ : beta = SpiderLegEnd.inward ∨ beta = SpiderLegEnd.outward) :
    spider_blocked_val beta r ∉ spider_blocked_optionvals r beta := by
  by_cases hr2 : 2 ≤ r
  · have hβ_ne : beta ≠ SpiderLegEnd.free := by
      rcases hβ with rfl | rfl <;> intro h <;> cases h
    by_cases hval : spider_blocked_val beta r = r + 1
    · intro hx
      have hle := spider_blocked_optionvals_le r hr2 beta hβ_ne _ hx
      rw [hval] at hle
      omega
    · rcases hβ with rfl | rfl
      · dsimp [spider_blocked_val] at hval
        have hr4 : r % 4 = 3 := by
          by_cases h : r % 4 = 3
          · exact h
          · rw [if_neg h] at hval; contradiction
        have hval_eq : spider_blocked_val SpiderLegEnd.inward r = r - 1 := by
          dsimp [spider_blocked_val]
          rw [if_pos hr4]
        rw [hval_eq]
        intro hmem
        simp only [spider_blocked_optionvals] at hmem
        rcases List.mem_append.mp hmem with hmem | hmem
        · rcases List.mem_append.mp hmem with hmem | hmem
          · rcases List.mem_flatMap.mp hmem with ⟨idx, hidx, hmem⟩
            simp only [List.mem_range] at hidx
            rcases List.mem_map.mp hmem with ⟨delta, hdelta, hx⟩
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hdelta
            rcases hdelta with rfl | rfl
            · have hpar := spider_blocked_optionvals_not_mem_cut_same_parity r (idx + 1) (by omega) (by omega) SpiderLegEnd.inward (Or.inl rfl)
              rw [hx] at hpar
              omega
            · exact spider_blocked_optionvals_not_mem_cut_diff_inward r (idx + 1) hr2 hr4 (by omega) (by omega) hx
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
            rw [spider_rho_zero_same SpiderLegEnd.inward (by decide), zero_xor] at hmem
            have h_even : (r - 1) % 2 = 0 := by omega
            have hval_even := spider_blocked_optionvals_not_mem_val_even SpiderLegEnd.inward (r - 1) h_even
            rw [hval_even] at hmem
            omega
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
          rcases hmem with h3a | h3b
          · dsimp [spider_rho] at h3a
            split_ifs at h3a <;> omega
          · rw [spider_blocked_optionvals_le_rho_star_ne_free r SpiderLegEnd.inward (by decide)] at h3b
            omega
      · dsimp [spider_blocked_val] at hval
        have hr4 : r % 4 = 1 := by
          by_cases h : r % 4 = 1
          · exact h
          · rw [if_neg h] at hval; contradiction
        have hval_eq : spider_blocked_val SpiderLegEnd.outward r = r - 1 := by
          dsimp [spider_blocked_val]
          rw [if_pos hr4]
        rw [hval_eq]
        intro hmem
        simp only [spider_blocked_optionvals] at hmem
        rcases List.mem_append.mp hmem with hmem | hmem
        · rcases List.mem_append.mp hmem with hmem | hmem
          · rcases List.mem_flatMap.mp hmem with ⟨idx, hidx, hmem⟩
            simp only [List.mem_range] at hidx
            rcases List.mem_map.mp hmem with ⟨delta, hdelta, hx⟩
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hdelta
            rcases hdelta with rfl | rfl
            · exact spider_blocked_optionvals_not_mem_cut_diff_outward r (idx + 1) hr2 hr4 (by omega) (by omega) hx
            · have hpar := spider_blocked_optionvals_not_mem_cut_same_parity r (idx + 1) (by omega) (by omega) SpiderLegEnd.outward (Or.inr rfl)
              rw [hx] at hpar
              omega
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
            rw [spider_rho_zero_same SpiderLegEnd.outward (by decide), zero_xor] at hmem
            have h_even : (r - 1) % 2 = 0 := by omega
            have hval_even := spider_blocked_optionvals_not_mem_val_even SpiderLegEnd.outward (r - 1) h_even
            rw [hval_even] at hmem
            omega
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
          rcases hmem with h3a | h3b
          · dsimp [spider_rho] at h3a
            omega
          · rw [spider_blocked_optionvals_le_rho_star_ne_free r SpiderLegEnd.outward (by decide)] at h3b
            omega
  · have hr1 : r = 1 := by omega
    subst hr1
    rcases hβ with rfl | rfl <;> decide
