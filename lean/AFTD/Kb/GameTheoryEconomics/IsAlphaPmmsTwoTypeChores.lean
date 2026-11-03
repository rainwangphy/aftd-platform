import AFTD.Prelude

/-!
# is_alpha_pmms_two_type_chores

Topic: fair_division   Node: 0e0d38c70178

Provenance: formalization of a published result. Source: arXiv:2610.19099; Aziz et al. 2017

For n agents indexed by Fin n with agent-specific chore cost functions p, q : Fin n → ℝ, an integer allocation x, y : Fin n → ℕ of two chore types is alpha-pairwise maximin share (alpha-PMMS) fair if for all distinct agents i, j : Fin n (i ≠ j) and all s, t : ℕ with s ≤ x i + x j and t ≤ y i + y j, agent i's cost p i * (x i : ℝ) + q i * (y i : ℝ) is at most alpha times the maximum of p i * (s : ℝ) + q i * (t : ℝ) and p i * ((x i + x j - s : ℕ) : ℝ) + q i * ((y i + y j - t : ℕ) : ℝ).
-/

/-- An allocation (x, y) of two chore types is alpha-PMMS fair if each agent's cost is at most alpha times the maximum part of any two-way split of the pooled chores with any other agent. -/
def is_alpha_pmms_two_type_chores (α : ℝ) {n : ℕ} (p q : Fin n → ℝ) (x y : Fin n → ℕ) : Prop :=
  ∀ (i j : Fin n), i ≠ j →
    ∀ (s t : ℕ), s ≤ x i + x j → t ≤ y i + y j →
      p i * (x i : ℝ) + q i * (y i : ℝ) ≤
        α * max (p i * (s : ℝ) + q i * (t : ℝ))
                (p i * ((x i + x j - s : ℕ) : ℝ) + q i * ((y i + y j - t : ℕ) : ℝ))
