import AFTD.Prelude

/-!
# is_positive_orthogonality_measure

Topic: combinatorics   Node: 50f755ee6d78

Provenance: formalization of a published result. Source: arXiv:2611.01561, Lemma 2.1

For N : ℕ, a polynomial sequence R : ℕ → Polynomial ℝ, a finite set S : Finset ℝ, and a weight function w : ℝ → ℝ, is_positive_orthogonality_measure N R S w holds if w(x) > 0 for all x ∈ S, for all i ≤ N and j ≤ N with i ≠ j the sum over x ∈ S of w(x) * (R i).eval x * (R j).eval x is 0, and for all i ≤ N the sum over x ∈ S of w(x) * ((R i)(x))^2 is strictly positive.
-/

/-- Predicate asserting that a weight function w on a finite set S is a positive orthogonality measure for a polynomial sequence R up to degree N. -/
def is_positive_orthogonality_measure (N : ℕ) (R : ℕ → Polynomial ℝ)
    (S : Finset ℝ) (w : ℝ → ℝ) : Prop := (∀ x ∈ S, 0 < w x) ∧
  (∀ i ≤ N, ∀ j ≤ N, i ≠ j →
    ∑ x ∈ S, w x * (R i).eval x * (R j).eval x = 0) ∧
  (∀ i ≤ N,
    0 < ∑ x ∈ S, w x * ((R i).eval x) ^ 2)
