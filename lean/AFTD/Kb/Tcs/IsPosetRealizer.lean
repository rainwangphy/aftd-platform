import AFTD.Prelude

/-!
# is_poset_realizer

Topic: combinatorics   Node: c1ab5f11b4a5

Provenance: formalization of a published result. Source: Dushnik and Miller, Partially ordered sets, Amer. J. Math. 63 (1941), pp. 600-620

Given a relation r : α → α → Prop on a type α and an indexed family R : ι → LinearOrder α of linear orders on α, is_poset_realizer r R is the proposition that for all x, y : α, r x y holds if and only if (R i).le x y holds for every i : ι.
-/

/-- A family of linear orders R realizes a relation r if r is their intersection. -/
def is_poset_realizer {α : Type*} (r : α → α → Prop) {ι : Type*} (R : ι → LinearOrder α) : Prop :=
  ∀ x y : α, r x y ↔ ∀ i, (R i).le x y
