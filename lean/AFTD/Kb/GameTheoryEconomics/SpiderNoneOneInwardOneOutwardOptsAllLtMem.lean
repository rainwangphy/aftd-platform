import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiderNoneOneInwardOneOutwardOpts
import AFTD.Kb.GameTheoryEconomics.SpiderRhoPairValues
import AFTD.Kb.GameTheoryEconomics.SpiderLegEnd
import AFTD.Kb.GameTheoryEconomics.SpiderRho

/-!
# spider_none_one_inward_one_outward_opts_all_lt_mem

Topic: combinatorial_games   Node: 041648ee490d

Provenance: helper lemma. step towards spider_blocked_none_one_inward_one_outward

For r ≥ 2 and φ ≠ free, every k < r is a member of the closed-form option list of the κ₁ family.
-/

/-- Every natural number below r occurs in the closed-form option list. -/
theorem spider_none_one_inward_one_outward_opts_all_lt_mem (r : ℕ) (hr : 2 ≤ r) (φ : SpiderLegEnd) (hφ : φ ≠ SpiderLegEnd.free) :
    ∀ k < r, k ∈ spider_none_one_inward_one_outward_opts r φ := by
  intro k hk
  have hr1 : 1 ≤ r - 1 := by omega
  rcases spider_rho_pair_values (r - 1) hr1 φ hφ with ⟨h0, h1⟩ | ⟨h1, h0⟩ <;>
    rw [spider_none_one_inward_one_outward_opts] <;>
    simp only [List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_range,
      List.not_mem_nil, or_false, h0, h1]
  · rcases Nat.lt_or_ge k 2 with hlt2 | hge2
    · interval_cases k <;> simp
    · by_cases hkr : k = r - 1
      · exact Or.inr hkr
      · have hle : k ≤ r - 2 := by omega
        rcases spider_rho_pair_values (r - 1 - k) (by omega) φ hφ with ⟨g0, g1⟩ | ⟨g1, g0⟩
        · refine Or.inl (Or.inr ⟨k - 1, by omega, Or.inl ?_⟩)
          have harg : r - 2 - (k - 1) = r - 1 - k := by omega
          rw [harg, g0, Nat.zero_xor]; omega
        · refine Or.inl (Or.inr ⟨k - 1, by omega, Or.inr ?_⟩)
          have harg : r - 2 - (k - 1) = r - 1 - k := by omega
          rw [harg, g0, Nat.zero_xor]; omega
  · rcases Nat.lt_or_ge k 2 with hlt2 | hge2
    · interval_cases k <;> simp
    · by_cases hkr : k = r - 1
      · exact Or.inr hkr
      · have hle : k ≤ r - 2 := by omega
        rcases spider_rho_pair_values (r - 1 - k) (by omega) φ hφ with ⟨g0, g1⟩ | ⟨g1, g0⟩
        · refine Or.inl (Or.inr ⟨k - 1, by omega, Or.inl ?_⟩)
          have harg : r - 2 - (k - 1) = r - 1 - k := by omega
          rw [harg, g0, Nat.zero_xor]; omega
        · refine Or.inl (Or.inr ⟨k - 1, by omega, Or.inr ?_⟩)
          have harg : r - 2 - (k - 1) = r - 1 - k := by omega
          rw [harg, g0, Nat.zero_xor]; omega
