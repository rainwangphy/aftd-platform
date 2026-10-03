import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsHareValidAssignment
import AFTD.Kb.GameTheoryEconomics.MonroeScore

/-!
# is_hare_monroe_committee

Topic: social_choice   Node: 118f69dea2f3

W is a winning committee of the (Hare) Monroe rule: some Hare-valid assignment for W has Monroe score at least that of every Hare-valid assignment of every size-k committee.
-/

/-- `W` is a winning committee of the (Hare) Monroe rule for approval ballots `A`. -/
def is_hare_monroe_committee {n m : ℕ} (A : Fin n → Finset (Fin m)) (k : ℕ)
    (W : Finset (Fin m)) : Prop :=
  ∃ π, is_hare_valid_assignment k W π ∧
    ∀ W' π', is_hare_valid_assignment k W' π' → monroe_score A π' ≤ monroe_score A π
