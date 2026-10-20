import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiderBlockedOptionvals
import AFTD.Kb.GameTheoryEconomics.SpiderBlockedVal
import AFTD.Kb.GameTheoryEconomics.SpiderRho
import AFTD.Kb.GameTheoryEconomics.SpiderRhoStar
import AFTD.Kb.GameTheoryEconomics.SpiderLegEnd

/-!
# spider_blocked_optionvals_low_mem

Topic: combinatorial_games   Node: 23735863a10b

Provenance: helper lemma. step towards spider_two_leg_blocked_incoming_val

For r ≥ 2, β inward or outward, and k + 2 ≤ r, the number k occurs in the explicit options list of (in;{(r,β),(1,free)}).
-/

lemma spider_blocked_optionvals_low_mem_mem_of_idx (r idx : ℕ) (beta delta : SpiderLegEnd)
    (hidx : idx < r - 1) (hδ : delta = SpiderLegEnd.inward ∨ delta = SpiderLegEnd.outward) :
    spider_rho (r - (idx + 1)) delta beta ^^^ spider_blocked_val delta idx
      ∈ spider_blocked_optionvals r beta := by
  unfold spider_blocked_optionvals
  refine List.mem_append_left _ (List.mem_append_left _ ?_)
  refine List.mem_flatMap.mpr ⟨idx, List.mem_range.mpr hidx, ?_⟩
  rcases hδ with rfl | rfl
  · exact List.mem_map.mpr ⟨_, by simp, rfl⟩
  · exact List.mem_map.mpr ⟨_, by simp, rfl⟩

lemma spider_blocked_optionvals_low_mem_exists_other (beta : SpiderLegEnd)
    (hβ : beta = SpiderLegEnd.inward ∨ beta = SpiderLegEnd.outward) :
    ∃ delta, (delta = SpiderLegEnd.inward ∨ delta = SpiderLegEnd.outward) ∧ delta ≠ beta := by
  rcases hβ with rfl | rfl
  · exact ⟨SpiderLegEnd.outward, Or.inr rfl, by simp⟩
  · exact ⟨SpiderLegEnd.inward, Or.inl rfl, by simp⟩

lemma spider_blocked_optionvals_low_mem_val_even (delta : SpiderLegEnd) (m : ℕ)
    (hm : Even m) : spider_blocked_val delta m = m + 1 := by
  have h3 : m % 4 ≠ 3 := by obtain ⟨k, rfl⟩ := hm; omega
  have h1 : m % 4 ≠ 1 := by obtain ⟨k, rfl⟩ := hm; omega
  cases delta with
  | free => simpa [spider_blocked_val] using h1
  | inward => simp [spider_blocked_val, h3]
  | outward => simp [spider_blocked_val, h1]

lemma spider_blocked_optionvals_low_mem_rho_self (h : ℕ) (beta : SpiderLegEnd)
    (hβ : beta = SpiderLegEnd.inward ∨ beta = SpiderLegEnd.outward) :
    spider_rho h beta beta = h % 2 := by
  rcases hβ with rfl | rfl <;> simp [spider_rho]

lemma spider_blocked_optionvals_low_mem_rho_other_odd (h : ℕ) (delta beta : SpiderLegEnd)
    (hβ : beta = SpiderLegEnd.inward ∨ beta = SpiderLegEnd.outward)
    (hδ : delta = SpiderLegEnd.inward ∨ delta = SpiderLegEnd.outward) (hne : delta ≠ beta)
    (hodd : h % 2 = 1) : spider_rho h delta beta = 0 := by
  rcases hβ with rfl | rfl <;> rcases hδ with rfl | rfl <;> simp_all [spider_rho]

lemma spider_blocked_optionvals_low_mem_rho_other_even (h : ℕ) (delta beta : SpiderLegEnd)
    (hβ : beta = SpiderLegEnd.inward ∨ beta = SpiderLegEnd.outward)
    (hδ : delta = SpiderLegEnd.inward ∨ delta = SpiderLegEnd.outward) (hne : delta ≠ beta)
    (heven : h % 2 = 0) (hge : 2 ≤ h) : spider_rho h delta beta = 1 := by
  rcases hβ with rfl | rfl <;> rcases hδ with rfl | rfl <;> simp_all [spider_rho]

/-- Coverage of the lower part [0, r-2] by the interior cuts of the blocked leg. -/
theorem spider_blocked_optionvals_low_mem (r k : ℕ) (hr : 2 ≤ r) (beta : SpiderLegEnd)
    (hβ : beta = SpiderLegEnd.inward ∨ beta = SpiderLegEnd.outward) (hk : k + 2 ≤ r) :
    k ∈ spider_blocked_optionvals r beta := by
  obtain ⟨c, rfl⟩ | ⟨c, rfl⟩ := Nat.even_or_odd k
  · obtain ⟨b, rfl⟩ | ⟨b, rfl⟩ := Nat.even_or_odd r
    · have hidx : c + c < b + b - 1 := by omega
      have hmem := spider_blocked_optionvals_low_mem_mem_of_idx (b + b) (c + c) beta beta hidx hβ
      have hval : spider_rho (b + b - (c + c + 1)) beta beta ^^^ spider_blocked_val beta (c + c)
          = c + c := by
        have hodd : (b + b - (c + c + 1)) % 2 = 1 := by omega
        rw [spider_blocked_optionvals_low_mem_rho_self _ _ hβ, hodd,
          spider_blocked_optionvals_low_mem_val_even _ _ ⟨c, rfl⟩,
          Nat.xor_comm, Nat.xor_one_of_odd ⟨c, by omega⟩]
        omega
      rwa [hval] at hmem
    · obtain ⟨delta, hδ, hne⟩ := spider_blocked_optionvals_low_mem_exists_other beta hβ
      have hidx : c + c < 2 * b + 1 - 1 := by omega
      have hmem := spider_blocked_optionvals_low_mem_mem_of_idx (2 * b + 1) (c + c) beta delta hidx hδ
      have hval : spider_rho (2 * b + 1 - (c + c + 1)) delta beta
          ^^^ spider_blocked_val delta (c + c) = c + c := by
        have heven : (2 * b + 1 - (c + c + 1)) % 2 = 0 := by omega
        have hge : 2 ≤ 2 * b + 1 - (c + c + 1) := by omega
        rw [spider_blocked_optionvals_low_mem_rho_other_even _ _ _ hβ hδ hne heven hge,
          spider_blocked_optionvals_low_mem_val_even _ _ ⟨c, rfl⟩,
          Nat.xor_comm, Nat.xor_one_of_odd ⟨c, by omega⟩]
        omega
      rwa [hval] at hmem
  · obtain ⟨b, rfl⟩ | ⟨b, rfl⟩ := Nat.even_or_odd r
    · obtain ⟨delta, hδ, hne⟩ := spider_blocked_optionvals_low_mem_exists_other beta hβ
      have hidx : c + c < b + b - 1 := by omega
      have hmem := spider_blocked_optionvals_low_mem_mem_of_idx (b + b) (c + c) beta delta hidx hδ
      have hval : spider_rho (b + b - (c + c + 1)) delta beta
          ^^^ spider_blocked_val delta (c + c) = 2 * c + 1 := by
        have hodd : (b + b - (c + c + 1)) % 2 = 1 := by omega
        rw [spider_blocked_optionvals_low_mem_rho_other_odd _ _ _ hβ hδ hne hodd,
          spider_blocked_optionvals_low_mem_val_even _ _ ⟨c, rfl⟩, Nat.zero_xor]
        omega
      rwa [hval] at hmem
    · have hidx : c + c < 2 * b + 1 - 1 := by omega
      have hmem := spider_blocked_optionvals_low_mem_mem_of_idx (2 * b + 1) (c + c) beta beta hidx hβ
      have hval : spider_rho (2 * b + 1 - (c + c + 1)) beta beta
          ^^^ spider_blocked_val beta (c + c) = 2 * c + 1 := by
        have heven : (2 * b + 1 - (c + c + 1)) % 2 = 0 := by omega
        rw [spider_blocked_optionvals_low_mem_rho_self _ _ hβ, heven,
          spider_blocked_optionvals_low_mem_val_even _ _ ⟨c, rfl⟩, Nat.zero_xor]
        omega
      rwa [hval] at hmem
