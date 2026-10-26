import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsEjrCommittee
import AFTD.Kb.GameTheoryEconomics.IsEjrCohesiveGroup

/-!
# is_ejr_committee_zero

Topic: social_choice   Node: 54fba70f3dd8

Provenance: helper lemma. step towards ejr_committee_monotone_chain_exists

For every approval profile with at least one voter, the empty committee is an EJR committee of size 0.
-/

/-- For every approval profile with at least one voter, the empty committee satisfies EJR at size 0. -/
theorem is_ejr_committee_zero {n m : ℕ} (A : Fin n → Finset (Fin m)) (hn : 0 < n) :
    is_ejr_committee A 0 ∅ := by
  constructor
  · simp
  · intro ℓ hℓ G hG
    simp only [is_ejr_cohesive_group] at hG
    simp at hG
    have : 0 < ℓ * n := Nat.mul_pos (by omega) hn
    omega
