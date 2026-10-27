import AFTD.Prelude
import AFTD.Kb.Tcs.UnitHammingTriangleFree

/-!
# unit_hamming_max_triangle_free

Topic: combinatorics   Node: 43ea36bd2e3d

Provenance: formalization of a published result. Source: arXiv:2610.32789 Definition 1.1

The maximum cardinality unit_hamming_max_triangle_free n q of a finite set A : Finset (Fin n → Fin q) satisfying unit_hamming_triangle_free A, defined as the supremum of cardinalities of such finite sets.
-/

/-- The maximum size T_q(n, 1) of a vertex subset of (Fin n → Fin q) inducing a triangle-free subgraph in the unit-distance Hamming graph. -/
noncomputable def unit_hamming_max_triangle_free (n q : ℕ) : ℕ := sSup {k : ℕ | ∃ A : Finset (Fin n → Fin q), unit_hamming_triangle_free A ∧ A.card = k}
