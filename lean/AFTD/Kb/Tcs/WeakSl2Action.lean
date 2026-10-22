import AFTD.Prelude

/-!
# weak_sl2_action

Topic: combinatorics   Node: 4fd6d4275ef9

Provenance: formalization of a published result. Source: arXiv:2610.24148, Section 2.5.3

Given a finite partially ordered type α with decidable equality, an integer-valued function rank : α → ℤ, and linear endomorphisms E, F, H : Module.End ℂ (α → ℂ), the predicate weak_sl2_action asserts that E * F - F * E = H, H * E - E * H = 2 • E, H * F - F * H = -2 • F, for every x : α we have H (Pi.single x 1) = (rank x : ℂ) • Pi.single x 1, and for all x y : α, if (E (Pi.single x 1)) y ≠ 0 then x ⋖ y.
-/

/-- A weak sl_2-action on a ranked poset with integer rank function. -/
def weak_sl2_action {α : Type*} [Fintype α] [DecidableEq α] [PartialOrder α]
    (rank : α → ℤ) (E F H : Module.End ℂ (α → ℂ)) : Prop :=
  E * F - F * E = H ∧
  H * E - E * H = 2 • E ∧
  H * F - F * H = -2 • F ∧
  (∀ x : α, H (Pi.single x (1 : ℂ)) = (rank x : ℂ) • Pi.single x (1 : ℂ)) ∧
  (∀ x y : α, (E (Pi.single x (1 : ℂ))) y ≠ 0 → x ⋖ y)
