import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GpaAdjMat
import AFTD.Kb.GameTheoryEconomics.GpaLhsSet
import AFTD.Kb.GameTheoryEconomics.GpaIndep
import AFTD.Kb.GameTheoryEconomics.GpaLhsUpper
import AFTD.Kb.GameTheoryEconomics.GpaLhsAttain

/-!
# gpa_lhs_isGreatest

Topic: mechanism_design   Node: 0efaecd38a7d

Exact value of the left side of Eq. (5.4) of arXiv:2209.01146 on the independent-set instances: max_{σ ∈ Δ_k} u*(σ) - h(σ) = 1 - 1/α(G) + 1/k.
-/

open Finset in
/-- Exact value of the left side of Eq. (5.4) of arXiv:2209.01146 on the independent-set instances: `max_{σ ∈ Δ_k} u*(σ) - h(σ) = 1 - 1/α(G) + 1/k`. -/
theorem gpa_lhs_isGreatest {k : ℕ} (G : SimpleGraph (Fin k)) [DecidableRel G.Adj]
    (I : Finset (Fin k)) (hI : gpa_indep G I) (hmax : ∀ S, gpa_indep G S → S.card ≤ I.card)
    (hne : 1 ≤ I.card) (hk : I.card ≤ k) :
    IsGreatest (gpa_lhsSet (gpa_adjMat G)) (1 - 1 / (I.card : ℝ) + 1 / (k : ℝ)) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨σ, hσ, hval⟩ := gpa_lhs_attain G I hI hne hk
    exact ⟨σ, hσ, hval⟩
  · rintro v ⟨σ, hσ, rfl⟩
    exact gpa_lhs_upper G I.card hne hmax σ hσ
