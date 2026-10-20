import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiderBlockedOptionvalsLowMem
import AFTD.Kb.GameTheoryEconomics.SpiderBlockedOptionvalsTopMem
import AFTD.Kb.GameTheoryEconomics.SpiderBlockedVal
import AFTD.Kb.GameTheoryEconomics.SpiderLegEnd
import AFTD.Kb.GameTheoryEconomics.SpiderBlockedOptionvals

/-!
# spider_blocked_optionvals_lt_mem

Topic: combinatorial_games   Node: 0574f6f50430

Provenance: helper lemma. step towards spider_two_leg_blocked_incoming_val

For r ≥ 2 and β inward or outward, every k below spider_blocked_val β r occurs in the explicit options list of (in;{(r,β),(1,free)}).
-/

/-- Gluing lemma: coverage of every k below the closed-form value, from the initial segment plus the two top values. -/
theorem spider_blocked_optionvals_lt_mem (r : ℕ) (hr : 2 ≤ r) (beta : SpiderLegEnd)
    (hβ : beta = SpiderLegEnd.inward ∨ beta = SpiderLegEnd.outward) :
    ∀ k < spider_blocked_val beta r, k ∈ spider_blocked_optionvals r beta := by
  intro k hk
  rcases hβ with rfl | rfl
  · by_cases h : r % 4 = 3
    · simp only [spider_blocked_val, h, if_true] at hk
      exact spider_blocked_optionvals_low_mem r k hr _ (Or.inl rfl) (by omega)
    · simp only [spider_blocked_val, h, if_false] at hk
      rcases Nat.lt_or_ge k r with hklt | hkge
      · rcases Nat.lt_or_ge k (r - 1) with h1 | h1
        · exact spider_blocked_optionvals_low_mem r k hr _ (Or.inl rfl) (by omega)
        · have hk_eq : k = r - 1 := by omega
          rw [hk_eq]
          exact (spider_blocked_optionvals_top_mem r (by omega) _ (Or.inl rfl)).2.1 rfl h
      · have hk_eq : k = r := by omega
        rw [hk_eq]
        exact (spider_blocked_optionvals_top_mem r (by omega) _ (Or.inl rfl)).1
  · by_cases h : r % 4 = 1
    · simp only [spider_blocked_val, h, if_true] at hk
      exact spider_blocked_optionvals_low_mem r k hr _ (Or.inr rfl) (by omega)
    · simp only [spider_blocked_val, h, if_false] at hk
      rcases Nat.lt_or_ge k r with hklt | hkge
      · rcases Nat.lt_or_ge k (r - 1) with h1 | h1
        · exact spider_blocked_optionvals_low_mem r k hr _ (Or.inr rfl) (by omega)
        · have hk_eq : k = r - 1 := by omega
          rw [hk_eq]
          exact (spider_blocked_optionvals_top_mem r (by omega) _ (Or.inr rfl)).2.2 rfl h
      · have hk_eq : k = r := by omega
        rw [hk_eq]
        exact (spider_blocked_optionvals_top_mem r (by omega) _ (Or.inr rfl)).1
