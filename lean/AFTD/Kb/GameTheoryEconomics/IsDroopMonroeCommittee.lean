import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsDroopValidAssignment
import AFTD.Kb.GameTheoryEconomics.DroopMonroeScore

/-!
# is_droop_monroe_committee

Topic: social_choice   Node: 3c362ba26f47

Provenance: formalization of a published result. Source: Justified Representation: From Hare to Droop, arXiv:2508.00811, Def. 16 (Droop Monroe rule)

W is a winning committee of the Droop Monroe rule: some Droop-valid assignment for W scores at least as much as every Droop-valid assignment of every size-k committee.
-/

/-- `W` is a winning committee of the Droop Monroe rule for approval ballots `A`. -/
def is_droop_monroe_committee {n m : ℕ} (A : Fin n → Finset (Fin m)) (k : ℕ)
    (W : Finset (Fin m)) : Prop :=
  ∃ π, is_droop_valid_assignment k W π ∧
    ∀ W' π', is_droop_valid_assignment k W' π' → droop_monroe_score A π' ≤ droop_monroe_score A π
