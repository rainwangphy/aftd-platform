import AFTD.Prelude

/-!
# word_critical_exponent

Topic: combinatorics   Node: ea2d596be177

Provenance: formalization of a published result. Source: arXiv:2611.13676 Sec. 1

The critical exponent of an infinite word w : ℕ → α is the supremum over all nonempty words x and factors y of w that are prefixes of powers of x of the ratio |y|/|x|.
-/

/-- The critical exponent of an infinite word is the supremum of rational powers |y|/|x| over all factors y with period x. -/
noncomputable def word_critical_exponent {α : Type*} (w : ℕ → α) : ℝ := sSup { e : ℝ | ∃ (x y : List α) (m : ℕ), x ≠ [] ∧
  (∃ i : ℕ, y = (List.range y.length).map (fun j => w (i + j))) ∧
  y <+: (List.replicate m x).flatten ∧ e = (y.length : ℝ) / (x.length : ℝ) }
