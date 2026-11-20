import AFTD.Prelude

/-!
# is_condorcet_winner

Topic: social_choice   Node: fa95724fa7c1

Provenance: formalization of a published result. Source: arXiv:2611.26224 Sec. 5.2, p. 10

Given a finite type of voters N, a profile of linear orders P : N → LinearOrder A on alternatives A, and an alternative x : A, is_condorcet_winner P x asserts that for every alternative y ≠ x, the number of voters who rank y < x in their linear order strictly exceeds half of the electorate, that is, Fintype.card N < 2 * (Finset.filter (fun i => (P i).lt y x) Finset.univ).card.
-/

/-- An alternative is a Condorcet winner if strictly more than half the voters strictly prefer it to every other alternative. -/
def is_condorcet_winner {N A : Type*} [Fintype N] (P : N → LinearOrder A) (x : A) : Prop :=
  ∀ y : A, y ≠ x →
    Fintype.card N < 2 * (Finset.filter (fun i => @LT.lt A (P i).toLT y x) Finset.univ).card
