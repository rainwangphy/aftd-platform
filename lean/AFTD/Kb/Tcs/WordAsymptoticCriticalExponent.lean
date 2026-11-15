import AFTD.Prelude

/-!
# word_asymptotic_critical_exponent

Topic: combinatorics   Node: 1211a786d0a1

Provenance: formalization of a published result. Source: arXiv:2611.13676 Sec. 1

The asymptotic critical exponent of an infinite word w is the real number defined as the real infimum (sInf) over all natural numbers N ≥ 1 of the real supremum (sSup) of the set of length ratios |y|/|x| in ℝ for all nonempty words x with length at least N and all factors y of w that are prefixes of finite powers of x.
-/

/-- The asymptotic critical exponent of an infinite word as a real number. -/
noncomputable def word_asymptotic_critical_exponent {α : Type*} (w : ℕ → α) : ℝ := sInf { r : ℝ | ∃ N : ℕ, 1 ≤ N ∧
    r = sSup { e : ℝ | ∃ (x y : List α) (m : ℕ), x ≠ [] ∧ N ≤ x.length ∧
      (∃ i : ℕ, y = (List.range y.length).map (fun j => w (i + j))) ∧
      y <+: (List.replicate m x).flatten ∧ e = (y.length : ℝ) / (x.length : ℝ) } }
