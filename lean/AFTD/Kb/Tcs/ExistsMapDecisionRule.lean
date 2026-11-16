import AFTD.Prelude

/-!
# exists_map_decision_rule

Topic: information   Node: 7dabbf8227b5

Provenance: helper lemma. arXiv:2611.16066 Proposition 3.1 -- Optimal Additive Integer Masks for One-Guess Vulnerability under an Absolute-Moment Budget

For any nonempty finite alphabet Fin m, prior p, and mask q on ℤ, there exists a decision rule g : ℤ → Fin m that attains the pointwise supremum p(g(s)) * q(s - g(s)) = ⨆ x, p(x) * q(s - x) for every integer observation s.
-/

/-- Existence of a MAP decision rule achieving the pointwise maximum. -/
lemma exists_map_decision_rule (m : ℕ) [NeZero m] (p : Fin m → ℝ) (q : ℤ → ℝ) : ∃ g : ℤ → Fin m, ∀ s : ℤ, p (g s) * q (s - g s) = ⨆ x : Fin m, p x * q (s - x) := by
  have h (s : ℤ) : ∃ x : Fin m, p x * q (s - x) = ⨆ x : Fin m, p x * q (s - x) :=
    exists_eq_ciSup_of_finite
  choose g hg using h
  exact ⟨g, hg⟩
