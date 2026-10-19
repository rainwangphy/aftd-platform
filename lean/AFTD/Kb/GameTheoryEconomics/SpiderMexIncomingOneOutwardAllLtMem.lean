import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiderRhoPairValues
import AFTD.Kb.GameTheoryEconomics.SpiderLegEnd
import AFTD.Kb.GameTheoryEconomics.SpiderRho

/-!
# spider_mex_incoming_one_outward_all_lt_mem

Topic: combinatorial_games   Node: 2733f030264a

Provenance: helper lemma. step towards spider_mex_incoming_one_outward

Every natural number k < r ^^^ 1 is a member of the explicit options list for (in;{(1,outward),(r,φ)}) when r ≥ 2 and φ ≠ free.
-/

/-- Every natural number strictly less than r ^^^ 1 is an element of the options list for the configuration κ₂ = (in;{(1,outward),(r,φ)}). -/
theorem spider_mex_incoming_one_outward_all_lt_mem (r : ℕ) (hr : 2 ≤ r) (φ : SpiderLegEnd) (hφ : φ ≠ SpiderLegEnd.free) :
    ∀ k < r ^^^ 1,
      k ∈
        ([r, spider_rho (r - 1) SpiderLegEnd.inward φ ^^^ 1, spider_rho (r - 1) SpiderLegEnd.outward φ ^^^ 1] ++
         (List.range (r - 2)).flatMap (fun idx =>
           let i := idx + 1
           [spider_rho (r - 1 - i) SpiderLegEnd.inward φ ^^^ (i ^^^ 1),
            spider_rho (r - 1 - i) SpiderLegEnd.outward φ ^^^ (i ^^^ 1)]) ++
         [spider_rho 0 φ φ ^^^ ((r - 1) ^^^ 1)]) := by
  let L_head := [r, spider_rho (r - 1) SpiderLegEnd.inward φ ^^^ 1, spider_rho (r - 1) SpiderLegEnd.outward φ ^^^ 1]
  let L_flat := (List.range (r - 2)).flatMap (fun idx =>
         let i := idx + 1
         [spider_rho (r - 1 - i) SpiderLegEnd.inward φ ^^^ (i ^^^ 1),
          spider_rho (r - 1 - i) SpiderLegEnd.outward φ ^^^ (i ^^^ 1)])
  let L_tail := [spider_rho 0 φ φ ^^^ ((r - 1) ^^^ 1)]

  have hh : 1 ≤ r - 1 := by omega
  have h_head : 0 ∈ L_head ∧ 1 ∈ L_head ∧ r ∈ L_head := by
    dsimp only [L_head]
    rcases spider_rho_pair_values (r - 1) hh φ hφ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; simp
    · rw [h1, h2]; simp

  have h_flat_i : ∀ i, 1 ≤ i → i ≤ r - 2 → i ∈ L_flat := by
    intro i hi1 hi2
    rw [List.mem_flatMap]
    refine ⟨i - 1, ?_, ?_⟩
    · rw [List.mem_range]; omega
    · dsimp only
      have : i - 1 + 1 = i := by omega
      rw [this]
      have hhi : 1 ≤ r - 1 - i := by omega
      rcases spider_rho_pair_values (r - 1 - i) hhi φ hφ with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2, zero_xor, xor_comm 1 (i ^^^ 1), xor_cancel_right]; simp
      · rw [h1, h2, zero_xor, xor_comm 1 (i ^^^ 1), xor_cancel_right]; simp

  have h_flat_xor : ∀ i, 1 ≤ i → i ≤ r - 2 → i ^^^ 1 ∈ L_flat := by
    intro i hi1 hi2
    rw [List.mem_flatMap]
    refine ⟨i - 1, ?_, ?_⟩
    · rw [List.mem_range]; omega
    · dsimp only
      have : i - 1 + 1 = i := by omega
      rw [this]
      have hhi : 1 ≤ r - 1 - i := by omega
      rcases spider_rho_pair_values (r - 1 - i) hhi φ hφ with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2, zero_xor, xor_comm 1 (i ^^^ 1), xor_cancel_right]; simp
      · rw [h1, h2, zero_xor, xor_comm 1 (i ^^^ 1), xor_cancel_right]; simp

  intro k hk
  change k ∈ L_head ++ L_flat ++ L_tail
  rcases Nat.even_or_odd r with he | ho
  · rw [Nat.xor_one_of_even he] at hk
    rcases lt_or_ge k 2 with hk01 | hk2
    · interval_cases k
      · simp [h_head.1]
      · simp [h_head.2.1]
    · rcases eq_or_lt_of_le (show k ≤ r by omega) with rfl | hkr
      · simp [h_head.2.2]
      · rcases eq_or_lt_of_le (show k ≤ r - 1 by omega) with rfl | hkr'
        · rcases he with ⟨m, rfl⟩
          have he' : Even (m + m - 2) := ⟨m - 1, by omega⟩
          have h_xor : (m + m - 2) ^^^ 1 = m + m - 1 := by
            rw [Nat.xor_one_of_even he']
            omega
          have h_mem : m + m - 1 ∈ L_flat := by
            rw [← h_xor]
            exact h_flat_xor (m + m - 2) (by omega) (by omega)
          simp [h_mem]
        · have h_mem : k ∈ L_flat := h_flat_i k (by omega) (by omega)
          simp [h_mem]
  · rw [Nat.xor_one_of_odd ho] at hk
    rcases lt_or_ge k 2 with hk01 | hk2
    · interval_cases k
      · simp [h_head.1]
      · simp [h_head.2.1]
    · have h_mem : k ∈ L_flat := h_flat_i k (by omega) (by omega)
      simp [h_mem]
