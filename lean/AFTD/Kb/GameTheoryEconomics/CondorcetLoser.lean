import AFTD.Prelude

/-!
# condorcet_loser

Topic: social_choice   Node: 8edbe48f562a

Provenance: formalization of a published result. Source: Fishburn 1977, 'Condorcet Social Choice Functions', SIAM Review 19(3): 469-489

In a profile of preferences P where a finite set of voters V have pairwise preferences over alternatives A, an alternative x : A is a Condorcet loser if for every alternative y ≠ x, the number of voters who strictly prefer y to x is strictly greater than the number of voters who strictly prefer x to y.
-/

/-- A Condorcet loser is defeated by every other alternative by strict pairwise majority. -/
def condorcet_loser {V A : Type*} [Fintype V]
    (P : V → A → A → Prop) [∀ v, DecidableRel (P v)] (x : A) : Prop := ∀ y : A, y ≠ x →
    (Finset.filter (fun v => P v y x) Finset.univ).card >
    (Finset.filter (fun v => P v x y) Finset.univ).card
