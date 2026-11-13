import AFTD.Prelude

/-!
# pyranim_is_visible

Topic: combinatorial_games   Node: 567ef5133ade

Provenance: formalization of a published result. Source: arXiv:2611.16153 Def. 1.2

For a finite set X : Finset (ℕ × ℕ) and a chip c : ℕ × ℕ, pyranim_is_visible X c is the proposition that c ∈ X and it is not the case that both (c.1 - 1, c.2) ∈ X and (c.1, c.2 + 1) ∈ X, with natural number subtraction on c.1 - 1.
-/

/-- A chip c in X is visible if its two immediate upper chips are not both present in X. -/
def pyranim_is_visible (X : Finset (ℕ × ℕ)) (c : ℕ × ℕ) : Prop := c ∈ X ∧ ¬ ((c.1 - 1, c.2) ∈ X ∧ (c.1, c.2 + 1) ∈ X)
