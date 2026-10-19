import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiderRhoPairValues
import AFTD.Kb.GameTheoryEconomics.SpiderRhoZeroSame
import AFTD.Kb.GameTheoryEconomics.SpiderLegEnd
import AFTD.Kb.GameTheoryEconomics.SpiderRho

/-!
# spider_mex_incoming_one_outward_not_mem

Topic: combinatorial_games   Node: 4552ca241b91

Provenance: helper lemma. step towards spider_mex_incoming_one_outward

The value r ^^^ 1 is not a member of the explicit options list for (in;{(1,outward),(r,φ)}) when r ≥ 2 and φ ≠ free.
-/

/-- The candidate mex value r ^^^ 1 is not an element of the options list for the configuration κ₂ = (in;{(1,outward),(r,φ)}). -/
theorem spider_mex_incoming_one_outward_not_mem (r : ℕ) (hr : 2 ≤ r) (φ : SpiderLegEnd) (hφ : φ ≠ SpiderLegEnd.free) :
    r ^^^ 1 ∉
      ([r, spider_rho (r - 1) SpiderLegEnd.inward φ ^^^ 1, spider_rho (r - 1) SpiderLegEnd.outward φ ^^^ 1] ++
       (List.range (r - 2)).flatMap (fun idx =>
         let i := idx + 1
         [spider_rho (r - 1 - i) SpiderLegEnd.inward φ ^^^ (i ^^^ 1),
          spider_rho (r - 1 - i) SpiderLegEnd.outward φ ^^^ (i ^^^ 1)]) ++
       [spider_rho 0 φ φ ^^^ ((r - 1) ^^^ 1)]) := by
  simp only [List.mem_append, not_or]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    have hh : 1 ≤ r - 1 := by omega
    rcases spider_rho_pair_values (r - 1) hh φ hφ with ⟨h_in, h_out⟩ | ⟨h_in, h_out⟩
    · rw [h_in, h_out] at h
      rcases h with h1 | h2 | h3
      · rcases Nat.even_or_odd r with he | ho
        · rw [Nat.xor_one_of_even he] at h1; omega
        · rw [Nat.xor_one_of_odd ho] at h1; omega
      · have : r = 0 := (xor_left_involutive 1).injective h2
        omega
      · have : r = 1 := (xor_left_involutive 1).injective h3
        omega
    · rw [h_in, h_out] at h
      rcases h with h1 | h2 | h3
      · rcases Nat.even_or_odd r with he | ho
        · rw [Nat.xor_one_of_even he] at h1; omega
        · rw [Nat.xor_one_of_odd ho] at h1; omega
      · have : r = 1 := (xor_left_involutive 1).injective h2
        omega
      · have : r = 0 := (xor_left_involutive 1).injective h3
        omega
  · intro h
    rw [List.mem_flatMap] at h
    rcases h with ⟨idx, hidx, hmem⟩
    rw [List.mem_range] at hidx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    let i := idx + 1
    have hi : i ≤ r - 2 := by omega
    have hh : 1 ≤ r - 1 - i := by omega
    rcases spider_rho_pair_values (r - 1 - i) hh φ hφ with ⟨h_in, h_out⟩ | ⟨h_in, h_out⟩
    · rw [h_in, h_out, zero_xor, xor_comm 1 (i ^^^ 1), xor_cancel_right] at hmem
      rcases hmem with h1 | h2
      · have : r = i := (xor_left_involutive 1).injective h1
        omega
      · rcases Nat.even_or_odd r with he | ho
        · rw [Nat.xor_one_of_even he] at h2; omega
        · rw [Nat.xor_one_of_odd ho] at h2; omega
    · rw [h_in, h_out, zero_xor, xor_comm 1 (i ^^^ 1), xor_cancel_right] at hmem
      rcases hmem with h1 | h2
      · rcases Nat.even_or_odd r with he | ho
        · rw [Nat.xor_one_of_even he] at h1; omega
        · rw [Nat.xor_one_of_odd ho] at h1; omega
      · have : r = i := (xor_left_involutive 1).injective h2
        omega
  · intro h
    simp only [List.mem_singleton] at h
    rw [spider_rho_zero_same φ hφ, zero_xor] at h
    have : r = r - 1 := (xor_left_involutive 1).injective h
    omega
