import AFTD.Prelude
import AFTD.Kb.Tcs.ComparisonEdge

/-!
# comparison_feature2

Topic: quantum   Node: 541b4b111cdb

Provenance: formalization of a published result. Source: arXiv:2610.34762 (Quantum ordinal selection with two comparisons), Section 3.1, the notation before Lemma 1

The type indexing the orthonormal coordinate basis of the formal quadratic feature space F_2 = span{1, d_e, d_e d_f}: the sum type of comparison_feature1 n (constant and linear coordinates, via `Sum.inl`) and the subtype of two-element Finsets {e, f} of edges (via `Sum.inr`), one quadratic coordinate for each unordered pair of distinct edges.
-/

/-- The type indexing the orthonormal coordinate basis of the formal quadratic feature space F_2 = span{1, d_e, d_e d_f}: the sum type of comparison_feature1 n (constant and linear coordinates, via `Sum.inl`) and the subtype of two-element Finsets {e, f} of edges (via `Sum.inr`), one quadratic coordinate for each unordered pair of distinct edges. -/
abbrev comparison_feature2 (n : ℕ) : Type := Option (comparison_edge n) ⊕ {s : Finset (comparison_edge n) // s.card = 2}
