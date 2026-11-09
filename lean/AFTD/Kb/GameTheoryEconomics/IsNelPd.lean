import AFTD.Prelude

/-!
# is_nel_pd

Topic: fair_division   Node: 9189ae26e5d1

Provenance: formalization of a published result. Source: arXiv:2611.09685 Section 3.1

An allocation A : Agent → Finset Object satisfies NEL under pairwise dominance with respect to item preferences le : Agent → Object → Object → Prop if whenever agent i receives strictly fewer objects than agent j, for every object y in A j there is an injection from (A j).erase y into A i mapping each object z to an object weakly preferred to z by agent i according to le i.
-/

/-- No envy toward larger bundles up to any object (NEL) under pairwise dominance. -/
def is_nel_pd {Agent Object : Type*} [DecidableEq Object] (le : Agent → Object → Object → Prop) (A : Agent → Finset Object) : Prop := ∀ (i j : Agent), (A i).card < (A j).card → ∀ y ∈ A j,
  ∃ (f : Object → Object), (∀ z ∈ (A j).erase y, f z ∈ A i) ∧
    (∀ z₁ ∈ (A j).erase y, ∀ z₂ ∈ (A j).erase y, f z₁ = f z₂ → z₁ = z₂) ∧
    ∀ z ∈ (A j).erase y, le i z (f z)
