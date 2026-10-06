import AFTD.Prelude

/-!
# droop_monroe_score

Topic: social_choice   Node: 55a143da8a8f

Provenance: formalization of a published result. Source: Justified Representation: From Hare to Droop, arXiv:2508.00811, Def. 16 (Monroe score of a Droop assignment)

Monroe score of a Droop assignment: the number of voters sent to a non-dummy candidate they approve.
-/

/-- Monroe score of a Droop assignment: voters sent to a (non-dummy) candidate they approve. -/
def droop_monroe_score {n m : ℕ} (A : Fin n → Finset (Fin m)) (π : Fin n → Option (Fin m)) :
    ℕ :=
  (Finset.univ.filter fun i => ∃ c, π i = some c ∧ c ∈ A i).card
