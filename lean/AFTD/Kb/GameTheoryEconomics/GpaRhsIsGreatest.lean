import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GpaAdjMat
import AFTD.Kb.GameTheoryEconomics.GpaRhsSet
import AFTD.Kb.GameTheoryEconomics.GpaIndep
import AFTD.Kb.GameTheoryEconomics.GpaRhsUpper
import AFTD.Kb.GameTheoryEconomics.GpaRhsAttain

/-!
# gpa_rhs_isGreatest

Topic: mechanism_design   Node: 70c5370d711a

Exact value of the right side of Eq. (5.4) of arXiv:2209.01146 (before the factor 1/k): max_{x ∈ [0,1]^k} u*(x) = α(G).
-/

open Finset in
/-- Exact value of the right side of Eq. (5.4) of arXiv:2209.01146 (before the factor `1/k`): `max_{x ∈ [0,1]^k} u*(x) = α(G)`. -/
theorem gpa_rhs_isGreatest {k : ℕ} (G : SimpleGraph (Fin k)) [DecidableRel G.Adj]
    (I : Finset (Fin k)) (hI : gpa_indep G I) (hmax : ∀ S, gpa_indep G S → S.card ≤ I.card) :
    IsGreatest (gpa_rhsSet (gpa_adjMat G)) (I.card : ℝ) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨hmem, hval⟩ := gpa_rhs_attain G I hI
    exact ⟨_, hmem, hval⟩
  · rintro v ⟨x, hx, rfl⟩
    exact gpa_rhs_upper G I.card hmax x hx
