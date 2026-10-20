import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiderBlockedOptionvals
import AFTD.Kb.GameTheoryEconomics.SpiderBlockedVal
import AFTD.Kb.GameTheoryEconomics.SpiderRho
import AFTD.Kb.GameTheoryEconomics.SpiderRhoStar
import AFTD.Kb.GameTheoryEconomics.SpiderLegEnd

/-!
# spider_blocked_optionvals_top_mem

Topic: combinatorial_games   Node: 464f3a237d56

Provenance: helper lemma. step towards spider_two_leg_blocked_incoming_val

For r ≥ 1 and β inward or outward, r is in the explicit options list; moreover r-1 is in it when β = inward and r % 4 ≠ 3, and when β = outward and r % 4 ≠ 1.
-/

lemma spider_blocked_optionvals_top_mem_last_inward (r : ℕ) :
    r ∈ spider_blocked_optionvals r SpiderLegEnd.inward := by
  have hmem : spider_rho_star r SpiderLegEnd.inward ∈ spider_blocked_optionvals r SpiderLegEnd.inward := by
    simp [spider_blocked_optionvals, List.mem_append]
  have hval : spider_rho_star r SpiderLegEnd.inward = r := rfl
  rwa [hval] at hmem

lemma spider_blocked_optionvals_top_mem_last_outward (r : ℕ) :
    r ∈ spider_blocked_optionvals r SpiderLegEnd.outward := by
  have hmem : spider_rho_star r SpiderLegEnd.outward ∈ spider_blocked_optionvals r SpiderLegEnd.outward := by
    simp [spider_blocked_optionvals, List.mem_append]
  have hval : spider_rho_star r SpiderLegEnd.outward = r := rfl
  rwa [hval] at hmem

lemma spider_blocked_optionvals_top_mem_mem_flatMap (r idx : ℕ) (beta delta : SpiderLegEnd)
    (hidx : idx < r - 1) (hδ : delta = SpiderLegEnd.inward ∨ delta = SpiderLegEnd.outward) :
    spider_rho (r - (idx + 1)) delta beta ^^^ spider_blocked_val delta idx ∈
      spider_blocked_optionvals r beta := by
  simp only [spider_blocked_optionvals]
  refine List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl ?_)))
  refine List.mem_flatMap.mpr ⟨idx, List.mem_range.mpr hidx, ?_⟩
  refine List.mem_map.mpr ⟨delta, ?_, ?_⟩
  · rcases hδ with rfl | rfl <;> simp
  · simp

lemma spider_blocked_optionvals_top_mem_rho_outward_inward_odd (h : ℕ) (hodd : h % 2 = 1) :
    spider_rho h SpiderLegEnd.outward SpiderLegEnd.inward = 0 := by
  simp [spider_rho, hodd]

lemma spider_blocked_optionvals_top_mem_rho_inward_outward_odd (h : ℕ) (hodd : h % 2 = 1) :
    spider_rho h SpiderLegEnd.inward SpiderLegEnd.outward = 0 := by
  simp [spider_rho, hodd]

lemma spider_blocked_optionvals_top_mem_inward_pred (r : ℕ) (hr2 : 2 ≤ r) (hmod : r % 4 ≠ 3) :
    r - 1 ∈ spider_blocked_optionvals r SpiderLegEnd.inward := by
  have hidx : r - 2 < r - 1 := by omega
  have hmem := spider_blocked_optionvals_top_mem_mem_flatMap r (r - 2) SpiderLegEnd.inward
    SpiderLegEnd.outward hidx (Or.inr rfl)
  have hh : r - (r - 2 + 1) = 1 := by omega
  have hrho : spider_rho (r - (r - 2 + 1)) SpiderLegEnd.outward SpiderLegEnd.inward = 0 := by
    rw [hh]
    exact spider_blocked_optionvals_top_mem_rho_outward_inward_odd 1 (by decide)
  have hmod' : (r - 2) % 4 ≠ 1 := by omega
  have hval : spider_blocked_val SpiderLegEnd.outward (r - 2) = r - 1 := by
    simp only [spider_blocked_val]
    rw [if_neg hmod']
    omega
  rw [hrho, hval, Nat.zero_xor] at hmem
  exact hmem

lemma spider_blocked_optionvals_top_mem_outward_pred (r : ℕ) (hr2 : 2 ≤ r) (hmod : r % 4 ≠ 1) :
    r - 1 ∈ spider_blocked_optionvals r SpiderLegEnd.outward := by
  have hidx : r - 2 < r - 1 := by omega
  have hmem := spider_blocked_optionvals_top_mem_mem_flatMap r (r - 2) SpiderLegEnd.outward
    SpiderLegEnd.inward hidx (Or.inl rfl)
  have hh : r - (r - 2 + 1) = 1 := by omega
  have hrho : spider_rho (r - (r - 2 + 1)) SpiderLegEnd.inward SpiderLegEnd.outward = 0 := by
    rw [hh]
    exact spider_blocked_optionvals_top_mem_rho_inward_outward_odd 1 (by decide)
  have hmod' : (r - 2) % 4 ≠ 3 := by omega
  have hval : spider_blocked_val SpiderLegEnd.inward (r - 2) = r - 1 := by
    simp only [spider_blocked_val]
    rw [if_neg hmod']
    omega
  rw [hrho, hval, Nat.zero_xor] at hmem
  exact hmem

/-- Coverage of the top values: r is always an option, and r-1 is an option outside the special residue class. -/
theorem spider_blocked_optionvals_top_mem (r : ℕ) (hr : 1 ≤ r) (beta : SpiderLegEnd)
    (hβ : beta = SpiderLegEnd.inward ∨ beta = SpiderLegEnd.outward) :
    r ∈ spider_blocked_optionvals r beta ∧
    (beta = SpiderLegEnd.inward → r % 4 ≠ 3 → r - 1 ∈ spider_blocked_optionvals r beta) ∧
    (beta = SpiderLegEnd.outward → r % 4 ≠ 1 → r - 1 ∈ spider_blocked_optionvals r beta) := by
  rcases hβ with rfl | rfl
  · refine ⟨spider_blocked_optionvals_top_mem_last_inward r, ?_, ?_⟩
    · intro _ hmod
      rcases Nat.lt_or_ge r 2 with h2 | h2
      · have h1 : r = 1 := by omega
        subst h1
        decide
      · exact spider_blocked_optionvals_top_mem_inward_pred r h2 hmod
    · intro h
      exact absurd h (by decide)
  · refine ⟨spider_blocked_optionvals_top_mem_last_outward r, ?_, ?_⟩
    · intro h
      exact absurd h (by decide)
    · intro _ hmod
      rcases Nat.lt_or_ge r 2 with h2 | h2
      · have h1 : r = 1 := by omega
        subst h1
        exact absurd (by decide : (1 : ℕ) % 4 = 1) hmod
      · exact spider_blocked_optionvals_top_mem_outward_pred r h2 hmod
