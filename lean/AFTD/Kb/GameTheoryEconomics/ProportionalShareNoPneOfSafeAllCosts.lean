import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsExPostSafeProcurementFor
import AFTD.Kb.GameTheoryEconomics.IsProcurementPne
import AFTD.Kb.GameTheoryEconomics.ProcurementAgentUtility
import AFTD.Kb.GameTheoryEconomics.ProcurementOthersBids
import AFTD.Kb.GameTheoryEconomics.ProcurementOthersBidsNonneg
import AFTD.Kb.GameTheoryEconomics.ProportionalShareAlloc
import AFTD.Kb.GameTheoryEconomics.ProportionalSharePay
import AFTD.Kb.GameTheoryEconomics.ProportionalShareUtilityEq

/-!
# proportional_share_no_pne_of_safe_all_costs

Topic: mechanism_design   Node: 36f4d4ce3ccf

If a proportional-share mechanism is ex-post safe for every nonnegative cost, then no profile with at least one agent and nonnegative costs is a pure Nash equilibrium.
-/

/-- Within proportional-share mechanisms, ex-post safety for every cost level rules out pure Nash equilibria altogether. -/
theorem proportional_share_no_pne_of_safe_all_costs (pool : ℝ → ℝ)
    (hsafe : ∀ c, 0 ≤ c →
      is_ex_post_safe_procurement_for proportional_share_alloc (proportional_share_pay pool) c)
    {n : ℕ} (hn : 0 < n) (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i) (β : Fin n → List ℝ) :
    ¬ is_procurement_pne proportional_share_alloc (proportional_share_pay pool) c β := by
  rintro ⟨hnn, hbr⟩
  let i : Fin n := ⟨0, hn⟩
  set others := procurement_others_bids β i
  have hR : 0 ≤ others.sum := List.sum_nonneg (procurement_others_bids_nonneg β hnn i)
  set u0 := procurement_agent_utility proportional_share_alloc (proportional_share_pay pool)
    (c i) (β i) others with hu0
  set C := c i + |u0| + 1 with hC
  obtain ⟨mine, hmine, hall, o, ho, hpos⟩ := hsafe C (by have := abs_nonneg u0; linarith [hc i])
  have hsC : 0 ≤ mine.sum := List.sum_nonneg hmine
  have hsCpos : 0 < mine.sum := by
    rcases hsC.lt_or_eq with h | h
    · exact h
    · rw [proportional_share_utility_eq, ← h, zero_div, zero_mul] at hpos; exact absurd hpos (lt_irrefl 0)
  have hpool : ∀ z, 0 ≤ z → C ≤ pool (mine.sum + z) := by
    intro z hz
    have := hall [z] (by simp; exact hz)
    rw [proportional_share_utility_eq, List.sum_singleton] at this
    have hp : 0 < mine.sum / (mine.sum + z) := div_pos hsCpos (by linarith)
    by_contra hlt; push Not at hlt
    have : mine.sum / (mine.sum + z) * (pool (mine.sum + z) - C) < 0 :=
      mul_neg_of_pos_of_neg hp (by linarith)
    linarith
  set t := mine.sum + |u0| * others.sum + 1 with ht
  have hab := abs_nonneg u0
  have htpos : 0 < t := by have := mul_nonneg hab hR; linarith
  have hdev := hbr i [t] (by simp; linarith)
  rw [proportional_share_utility_eq (pool := pool) (c := c i) (mine := [t]), List.sum_singleton] at hdev
  have hW : 0 < t + others.sum := by linarith
  have hpW : C ≤ pool (t + others.sum) := by
    have := hpool (|u0| * others.sum + 1 + others.sum) (by have := mul_nonneg hab hR; linarith)
    convert this using 2; rw [ht]; ring
  have hfrac : 0 ≤ t / (t + others.sum) := div_nonneg htpos.le hW.le
  have h1 : t / (t + others.sum) * (|u0| + 1) ≤ t / (t + others.sum) * (pool (t + others.sum) - c i) :=
    mul_le_mul_of_nonneg_left (by linarith) hfrac
  have h2 : |u0| < t / (t + others.sum) * (|u0| + 1) := by
    rw [div_mul_eq_mul_div, lt_div_iff₀ hW]
    have := mul_nonneg hab hR
    nlinarith
  have h3 := le_abs_self u0
  linarith
