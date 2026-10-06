import AFTD.Prelude

/-!
# monroe_score

Topic: social_choice   Node: 3490d10b8aea

Provenance: formalization of a published result. Source: Justified Representation: From Hare to Droop, arXiv:2508.00811, Def. 16 (Monroe score of an assignment)

The Monroe score of an assignment π: the number of voters i with π(i) ∈ A_i.
-/

/-- Monroe score of an assignment: the number of voters assigned to a candidate they approve. -/
def monroe_score {n m : ℕ} (A : Fin n → Finset (Fin m)) (π : Fin n → Fin m) : ℕ :=
  (Finset.univ.filter fun i => π i ∈ A i).card
