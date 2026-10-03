import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ApxQuota
import AFTD.Kb.GameTheoryEconomics.ApxAllVectors

/-!
# apx_candidates

Topic: social_choice   Node: 62fb3458bcea

The quota-compliant seat vectors of a four-state profile at house size 8.
-/

/-- The quota-compliant seat vectors for profile `p` at house size 8. -/
def apx_candidates (p : Fin 4 → ℕ) : List (Fin 4 → ℕ) :=
  apx_all_vectors.filter (apx_quota p 8)
