import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetWinner

/-!
# condorcet_winner_not_of_majority_defeated

Topic: social_choice   Node: 948cd01017d9

If an alternative y is strictly preferred to alternative x by more voters than prefer x to y, then x cannot be a Condorcet winner.
-/

/-- An alternative that is strictly defeated in pairwise majority comparison cannot be a Condorcet winner. -/
theorem condorcet_winner_not_of_majority_defeated {V A : Type*} [Fintype V]
    (P : V → A → A → Prop) [∀ v, DecidableRel (P v)] (x y : A)
    (h_defeat : (Finset.filter (fun v => P v y x) Finset.univ).card >
                (Finset.filter (fun v => P v x y) Finset.univ).card) :
    ¬ condorcet_winner P x := by
  intro hx
  by_cases h : y = x
  · subst h
    omega
  · have h1 := hx y h
    omega
