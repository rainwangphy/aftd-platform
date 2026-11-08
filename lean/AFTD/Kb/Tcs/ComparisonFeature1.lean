import AFTD.Prelude
import AFTD.Kb.Tcs.ComparisonEdge

/-!
# comparison_feature1

Topic: quantum   Node: 1e4dcdd76ae5

Provenance: formalization of a published result. Source: arXiv:2610.34762 (Quantum ordinal selection with two comparisons), Section 3.1, the notation before Lemma 1

The type indexing the orthonormal coordinate basis of the formal linear feature space F_1 = span{1, d_e}: Option (comparison_edge n), where `none` is the coordinate of the constant feature 1 and `some e` the coordinate of the sign feature d_e of the edge e.
-/

/-- The type indexing the orthonormal coordinate basis of the formal linear feature space F_1 = span{1, d_e}: Option (comparison_edge n), where `none` is the coordinate of the constant feature 1 and `some e` the coordinate of the sign feature d_e of the edge e. -/
abbrev comparison_feature1 (n : ℕ) : Type := Option (comparison_edge n)
