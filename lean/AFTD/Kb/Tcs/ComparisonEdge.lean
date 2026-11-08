import AFTD.Prelude

/-!
# comparison_edge

Topic: quantum   Node: bf7f8c340db5

Provenance: formalization of a published result. Source: arXiv:2610.34762 (Quantum ordinal selection with two comparisons), Section 3.1, the notation before Lemma 1

The type of edges of the label set [n] = Fin n: the subtype of pairs (a, b) in Fin n × Fin n with a < b, each unordered edge {a, b} being stored once with its smaller label first.
-/

/-- The type of edges of the label set [n] = Fin n: the subtype of pairs (a, b) in Fin n × Fin n with a < b, each unordered edge {a, b} being stored once with its smaller label first. -/
abbrev comparison_edge (n : ℕ) : Type := {p : Fin n × Fin n // p.1 < p.2}
