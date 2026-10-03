import AFTD.Prelude

/-!
# droop_monroe_tie_ballot

Topic: social_choice   Node: d04f909afd63

Ballots of the Droop Monroe tie example: three voters approving {0,1,3}, {0,1,3} and {0,2,3}.
-/

/-- Ballots of the tie example: voters approve {0,1,3}, {0,1,3} and {0,2,3}. -/
def droop_monroe_tie_ballot : Fin 3 → Finset (Fin 4) := ![{0, 1, 3}, {0, 1, 3}, {0, 2, 3}]
