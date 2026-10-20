import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiderNoneOneInwardOneOutwardOpts
import AFTD.Kb.GameTheoryEconomics.SpiderRhoPairValues
import AFTD.Kb.GameTheoryEconomics.SpiderLegEnd
import AFTD.Kb.GameTheoryEconomics.SpiderRho

/-!
# spider_none_one_inward_one_outward_opts_not_mem

Topic: combinatorial_games   Node: 463cd962faf5

Provenance: helper lemma. step towards spider_blocked_none_one_inward_one_outward

For r ≥ 2 and φ ≠ free, the level r is not a member of the closed-form option list of the κ₁ family.
-/

/-- Xor with 1 changes the lowest bit, so it never fixes a number. -/
lemma spider_none_one_inward_one_outward_opts_not_mem_xor_one_ne (a : ℕ) : a ^^^ 1 ≠ a := by
  intro h
  have h2 := congrArg (fun n => n.testBit 0) h
  simp only [Nat.testBit_xor] at h2
  simp at h2

/-- For a nonzero leg height and a non-free end, every `spider_rho` value for the two
directions is `0` or `1`. -/
lemma spider_none_one_inward_one_outward_opts_not_mem_rho_le_one (h : ℕ) (hh : 1 ≤ h)
    (φ : SpiderLegEnd) (hφ : φ ≠ SpiderLegEnd.free) (d : SpiderLegEnd)
    (hd : d = SpiderLegEnd.inward ∨ d = SpiderLegEnd.outward) : spider_rho h d φ ≤ 1 := by
  rcases spider_rho_pair_values h hh φ hφ with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rcases hd with rfl | rfl <;> omega
  · rcases hd with rfl | rfl <;> omega

/-- Xoring a number at most `1` with `n` increases it by at most one. -/
lemma spider_none_one_inward_one_outward_opts_not_mem_xor_le_succ (x n : ℕ) (hx : x ≤ 1) :
    x ^^^ n ≤ n + 1 := by
  interval_cases x
  · simp
  · rw [Nat.xor_comm]
    rcases Nat.even_or_odd n with h | h
    · rw [Nat.xor_one_of_even h]
    · rw [Nat.xor_one_of_odd h]; omega

/-- The value r itself is absent from the closed-form option list. -/
theorem spider_none_one_inward_one_outward_opts_not_mem (r : ℕ) (hr : 2 ≤ r) (φ : SpiderLegEnd) (hφ : φ ≠ SpiderLegEnd.free) :
    r ∉ spider_none_one_inward_one_outward_opts r φ := by
  rw [spider_none_one_inward_one_outward_opts]
  simp only [List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_range,
    List.not_mem_nil, List.cons_append, List.nil_append]
  rintro (h | h | h | h | ⟨a, ha, h | h | h⟩ | h | h)
  · exact spider_none_one_inward_one_outward_opts_not_mem_xor_one_ne r h.symm
  · exact spider_none_one_inward_one_outward_opts_not_mem_xor_one_ne r h.symm
  · have := spider_none_one_inward_one_outward_opts_not_mem_rho_le_one (r - 1) (by omega) φ hφ
      SpiderLegEnd.inward (Or.inl rfl)
    omega
  · have := spider_none_one_inward_one_outward_opts_not_mem_rho_le_one (r - 1) (by omega) φ hφ
      SpiderLegEnd.outward (Or.inr rfl)
    omega
  · have hb := spider_none_one_inward_one_outward_opts_not_mem_rho_le_one (r - 2 - a) (by omega) φ hφ
      SpiderLegEnd.inward (Or.inl rfl)
    have := spider_none_one_inward_one_outward_opts_not_mem_xor_le_succ
      (spider_rho (r - 2 - a) SpiderLegEnd.inward φ) (a + 1) hb
    omega
  · have hb := spider_none_one_inward_one_outward_opts_not_mem_rho_le_one (r - 2 - a) (by omega) φ hφ
      SpiderLegEnd.outward (Or.inr rfl)
    have := spider_none_one_inward_one_outward_opts_not_mem_xor_le_succ
      (spider_rho (r - 2 - a) SpiderLegEnd.outward φ) (a + 1) hb
    omega
  · exact h.elim
  · omega
  · exact h
