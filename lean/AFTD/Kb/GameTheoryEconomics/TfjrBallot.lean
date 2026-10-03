import AFTD.Prelude

/-!
# tfjr_ballot

Topic: social_choice   Node: 07e97c10c01a

Ballots of the Droop-FJR vs BFJR counterexample: voter 0 approves candidate 0 in rounds 0-2, voter 1 approves candidate 0 in rounds 3-5, voters 2 and 3 approve candidate 1 in every round.
-/

/-- Ballots of the counterexample: voter 0 approves candidate 0 in rounds 0–2 only, voter 1 approves candidate 0 in rounds 3–5 only, voters 2 and 3 approve candidate 1 in every round. -/
def tfjr_ballot : Fin 4 → Fin 6 → Finset (Fin 2) := fun i r =>
  if i = 0 then (if r.val < 3 then {0} else ∅)
  else if i = 1 then (if 3 ≤ r.val then {0} else ∅) else {1}
