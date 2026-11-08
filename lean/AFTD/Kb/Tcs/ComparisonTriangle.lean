import AFTD.Prelude

/-!
# comparison_triangle

Topic: quantum   Node: 786f6b173e1e

Provenance: formalization of a published result. Source: arXiv:2610.34762 (Quantum ordinal selection with two comparisons), Section 3.1, the notation before Lemma 1

The type of triangles of the label set [n] = Fin n: the subtype of triples (a, (b, c)) in Fin n × Fin n × Fin n with a < b and b < c.
-/

/-- The type of triangles of the label set [n] = Fin n: the subtype of triples (a, (b, c)) in Fin n × Fin n × Fin n with a < b and b < c. -/
abbrev comparison_triangle (n : ℕ) : Type := {t : Fin n × Fin n × Fin n // t.1 < t.2.1 ∧ t.2.1 < t.2.2}
