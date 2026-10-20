import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiderBlockedOptionvals
import AFTD.Kb.GameTheoryEconomics.SpiderBlockedVal
import AFTD.Kb.GameTheoryEconomics.SpiderRho
import AFTD.Kb.GameTheoryEconomics.SpiderRhoStar
import AFTD.Kb.GameTheoryEconomics.SpiderLegEnd
import AFTD.Kb.GameTheoryEconomics.SpiderRhoZeroSame

/-!
# spider_blocked_optionvals_le

Topic: combinatorial_games   Node: 8165b2e2069c

Provenance: helper lemma. step towards spider_two_leg_blocked_incoming_val

For r ≥ 2 and β ≠ free, every element of the explicit options list of (in;{(r,β),(1,free)}) is at most r.
-/

lemma spider_blocked_optionvals_le_xor_one_le (b : ℕ) : b ^^^ 1 ≤ b + 1 := by
  rcases Nat.even_or_odd b with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [Nat.xor_one_of_even ⟨k, hk⟩]
  · rw [Nat.xor_one_of_odd ⟨k, hk⟩]
    omega

lemma spider_blocked_optionvals_le_xor_le_succ (a b : ℕ) (ha : a ≤ 1) : a ^^^ b ≤ b + 1 := by
  interval_cases a
  · simp
  · rw [Nat.xor_comm]; exact spider_blocked_optionvals_le_xor_one_le b

lemma spider_blocked_optionvals_le_rho_le_one (h : ℕ) (delta beta : SpiderLegEnd)
    (hβ : beta ≠ SpiderLegEnd.free) : spider_rho h delta beta ≤ 1 := by
  rcases beta with _ | _ | _
  · exact absurd rfl hβ
  · simp only [spider_rho]
    split_ifs with h1 h2
    · have := Nat.mod_lt h (by norm_num : 0 < 2); omega
    · omega
    · omega
  · simp only [spider_rho]
    split_ifs with h1 h2
    · have := Nat.mod_lt h (by norm_num : 0 < 2); omega
    · omega
    · omega

lemma spider_blocked_optionvals_le_rho_star_ne_free (h : ℕ) (phi : SpiderLegEnd)
    (hφ : phi ≠ SpiderLegEnd.free) : spider_rho_star h phi = h := by
  rcases phi with _ | _ | _ <;> simp [spider_rho_star] at *

lemma spider_blocked_optionvals_le_val_le_succ (delta : SpiderLegEnd) (m : ℕ) :
    spider_blocked_val delta m ≤ m + 1 := by
  rcases delta with _ | _ | _ <;> simp only [spider_blocked_val] <;> split_ifs <;> omega

/-- Bound on the options of the blocked two-leg family: all lie in [0, r]. -/
theorem spider_blocked_optionvals_le (r : ℕ) (hr : 2 ≤ r) (beta : SpiderLegEnd)
    (hβ : beta ≠ SpiderLegEnd.free) : ∀ x ∈ spider_blocked_optionvals r beta, x ≤ r := by
  intro x hx
  simp only [spider_blocked_optionvals] at hx
  rcases List.mem_append.mp hx with hx | hx
  · rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_flatMap.mp hx with ⟨idx, hidx, hx⟩
      simp only [List.mem_range] at hidx
      rcases List.mem_map.mp hx with ⟨delta, hdelta, hx⟩
      rw [← hx]
      have hrho := spider_blocked_optionvals_le_rho_le_one (r - (idx + 1)) delta beta hβ
      have hval := spider_blocked_optionvals_le_val_le_succ delta (idx + 1 - 1)
      have hxor := spider_blocked_optionvals_le_xor_le_succ
        (spider_rho (r - (idx + 1)) delta beta) (spider_blocked_val delta (idx + 1 - 1)) hrho
      omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      subst hx
      rw [spider_rho_zero_same beta hβ, Nat.zero_xor]
      have := spider_blocked_optionvals_le_val_le_succ beta (r - 1)
      omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · have := spider_blocked_optionvals_le_rho_le_one r SpiderLegEnd.outward beta hβ
      omega
    · rw [spider_blocked_optionvals_le_rho_star_ne_free r beta hβ]
