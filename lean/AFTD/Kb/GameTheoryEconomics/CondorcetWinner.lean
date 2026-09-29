import AFTD.Prelude

/-!
# condorcet_winner

Topic: social_choice   Node: 7cab8a8d4d93

In a profile of preferences P where a finite set of voters V have pairwise preferences over alternatives A, an alternative x : A is a Condorcet winner if for every alternative y ≠ x, the number of voters who strictly prefer x to y is strictly greater than the number of voters who strictly prefer y to x.
-/

/-- An alternative is a Condorcet winner if it strictly defeats every other alternative in pairwise majority comparison. -/
def condorcet_winner {V A : Type*} [Fintype V]
    (P : V → A → A → Prop) [∀ v, DecidableRel (P v)] (x : A) : Prop := ∀ y : A, y ≠ x →
    (Finset.filter (fun v => P v x y) Finset.univ).card >
    (Finset.filter (fun v => P v y x) Finset.univ).card
