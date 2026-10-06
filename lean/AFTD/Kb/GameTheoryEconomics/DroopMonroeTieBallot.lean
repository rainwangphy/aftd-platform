import AFTD.Prelude

/-!
# droop_monroe_tie_ballot

Topic: social_choice   Node: d04f909afd63

Provenance: helper lemma. step towards droop_monroe_tie_violates_droop_ejr_plus_fjr (tie example for Justified Representation: From Hare to Droop, arXiv:2508.00811, Table 1)

Ballots of the Droop Monroe tie example: three voters approving {0,1,3}, {0,1,3} and {0,2,3}.
-/

/-- Ballots of the tie example: voters approve {0,1,3}, {0,1,3} and {0,2,3}. -/
def droop_monroe_tie_ballot : Fin 3 → Finset (Fin 4) := ![{0, 1, 3}, {0, 1, 3}, {0, 2, 3}]
