import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.NatXorModTwo
import AFTD.Kb.GameTheoryEconomics.NatMexListEqOne
import AFTD.Kb.GameTheoryEconomics.SpiderLegEnd
import AFTD.Kb.GameTheoryEconomics.NatMexListEqZero
import AFTD.Kb.GameTheoryEconomics.NatMexList
import AFTD.Kb.GameTheoryEconomics.CentreStatus
import AFTD.Kb.GameTheoryEconomics.SpiderGamma

/-!
# spider_mex_two_leg_one_free

Topic: combinatorial_games   Node: 5b6c0e24fb5e

Provenance: helper lemma. step towards spider_two_leg_one_free

Given an explicit options list where every element has parity k % 2, the minimum excluded value is 1 - k % 2 (which is 1 when k is even, since 0 is in the list and all elements are even; and 0 when k is odd, since all elements are odd).
-/

theorem spider_mex_two_leg_one_free_parity (k : ℕ) (hk : 1 ≤ k)
    (h_parity : ∀ (idx : ℕ) (delta : SpiderLegEnd), idx < k - 1 →
      delta = SpiderLegEnd.inward ∨ delta = SpiderLegEnd.outward →
      spider_gamma (k + 1) CentreStatus.incoming [(idx + 1, delta), (1, SpiderLegEnd.free)] % 2 = (idx + 2) % 2)
    (x : ℕ)
    (hx : x ∈ [k, k % 2, (k - 1) ^^^ 1, (k - 1) ^^^ 1] ++
       (List.range (k - 1)).flatMap (fun idx =>
         let j := idx + 2
         let d := k - j
         [SpiderLegEnd.inward, SpiderLegEnd.outward].map (fun delta =>
           d ^^^ spider_gamma (k + 1) CentreStatus.incoming [(idx + 1, delta), (1, SpiderLegEnd.free)]
         )
       )) :
    x % 2 = k % 2 := by
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
             List.mem_flatMap, List.mem_range, List.mem_map] at hx
  rcases hx with (rfl | rfl | rfl | rfl) | ⟨idx, hidx, delta, hdelta, rfl⟩
  · rfl
  · rw [Nat.mod_mod]
  · rw [nat_xor_mod_two]
    omega
  · rw [nat_xor_mod_two]
    omega
  · rw [nat_xor_mod_two]
    rcases hdelta with (rfl | rfl)
    · have hp := h_parity idx SpiderLegEnd.inward hidx (Or.inl rfl)
      omega
    · have hp := h_parity idx SpiderLegEnd.outward hidx (Or.inr rfl)
      omega

/-- The mex of the options list for two free legs 1 and k equals 1 - k % 2, assuming each subgame option has parity (idx + 2) % 2. -/
theorem spider_mex_two_leg_one_free (k : ℕ) (hk : 1 ≤ k)
    (h_parity : ∀ (idx : ℕ) (delta : SpiderLegEnd), idx < k - 1 →
      delta = SpiderLegEnd.inward ∨ delta = SpiderLegEnd.outward →
      spider_gamma (k + 1) CentreStatus.incoming [(idx + 1, delta), (1, SpiderLegEnd.free)] % 2 = (idx + 2) % 2) :
    nat_mex_list
      ([k, k % 2, (k - 1) ^^^ 1, (k - 1) ^^^ 1] ++
       (List.range (k - 1)).flatMap (fun idx =>
         let j := idx + 2
         let d := k - j
         [SpiderLegEnd.inward, SpiderLegEnd.outward].map (fun delta =>
           d ^^^ spider_gamma (k + 1) CentreStatus.incoming [(idx + 1, delta), (1, SpiderLegEnd.free)]
         )
       )) = 1 - k % 2 := by
  have h_all : ∀ x ∈ ([k, k % 2, (k - 1) ^^^ 1, (k - 1) ^^^ 1] ++
       (List.range (k - 1)).flatMap (fun idx =>
         let j := idx + 2
         let d := k - j
         [SpiderLegEnd.inward, SpiderLegEnd.outward].map (fun delta =>
           d ^^^ spider_gamma (k + 1) CentreStatus.incoming [(idx + 1, delta), (1, SpiderLegEnd.free)]
         )
       )), x % 2 = k % 2 := by
    intro x hx
    exact spider_mex_two_leg_one_free_parity k hk h_parity x hx
  rcases Nat.mod_two_eq_zero_or_one k with hk0 | hk1
  · have h0 : 0 ∈ ([k, k % 2, (k - 1) ^^^ 1, (k - 1) ^^^ 1] ++
       (List.range (k - 1)).flatMap (fun idx =>
         let j := idx + 2
         let d := k - j
         [SpiderLegEnd.inward, SpiderLegEnd.outward].map (fun delta =>
           d ^^^ spider_gamma (k + 1) CentreStatus.incoming [(idx + 1, delta), (1, SpiderLegEnd.free)]
         )
       )) := by
      simp only [List.mem_append, List.mem_cons]
      left; right; left
      exact hk0.symm
    have h1 : 1 ∉ ([k, k % 2, (k - 1) ^^^ 1, (k - 1) ^^^ 1] ++
       (List.range (k - 1)).flatMap (fun idx =>
         let j := idx + 2
         let d := k - j
         [SpiderLegEnd.inward, SpiderLegEnd.outward].map (fun delta =>
           d ^^^ spider_gamma (k + 1) CentreStatus.incoming [(idx + 1, delta), (1, SpiderLegEnd.free)]
         )
       )) := by
      intro h1_in
      have := h_all 1 h1_in
      rw [hk0] at this
      omega
    rw [nat_mex_list_eq_one _ h0 h1]
    omega
  · have h0 : 0 ∉ ([k, k % 2, (k - 1) ^^^ 1, (k - 1) ^^^ 1] ++
       (List.range (k - 1)).flatMap (fun idx =>
         let j := idx + 2
         let d := k - j
         [SpiderLegEnd.inward, SpiderLegEnd.outward].map (fun delta =>
           d ^^^ spider_gamma (k + 1) CentreStatus.incoming [(idx + 1, delta), (1, SpiderLegEnd.free)]
         )
       )) := by
      intro h0_in
      have := h_all 0 h0_in
      rw [hk1] at this
      omega
    rw [nat_mex_list_eq_zero _ h0]
    omega
