import AFTD.Prelude

/-!
# is_ef1_pd

Topic: fair_division   Node: 4177b938d1bd

Provenance: formalization of a published result. Source: arXiv:2611.09685 Section 3

An allocation A : Agent → Finset Object satisfies EF1 under pairwise dominance with respect to item preferences le : Agent → Object → Object → Prop if for all agents i and j, either there is an injection from A j into A i mapping each object to a weakly preferred object according to le i, or for some object y in A j there is an injection from (A j).erase y into A i mapping each object to a weakly preferred object according to le i.
-/

/-- Envy-freeness up to one object (EF1) under pairwise dominance. -/
def is_ef1_pd {Agent Object : Type*} [DecidableEq Object] (le : Agent → Object → Object → Prop) (A : Agent → Finset Object) : Prop := ∀ (i j : Agent),
  (∃ (f : Object → Object), (∀ z ∈ A j, f z ∈ A i) ∧
    (∀ z₁ ∈ A j, ∀ z₂ ∈ A j, f z₁ = f z₂ → z₁ = z₂) ∧
    ∀ z ∈ A j, le i z (f z)) ∨
  ∃ y ∈ A j, ∃ (f : Object → Object), (∀ z ∈ (A j).erase y, f z ∈ A i) ∧
    (∀ z₁ ∈ (A j).erase y, ∀ z₂ ∈ (A j).erase y, f z₁ = f z₂ → z₁ = z₂) ∧
    ∀ z ∈ (A j).erase y, le i z (f z)
