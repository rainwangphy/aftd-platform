import AFTD.Prelude

/-!
# vector_seq_max_entry

Topic: combinatorics   Node: 48058c8151e9

Provenance: formalization of a published result. Source: arXiv:2610.26970 Def 1.1

The maximum entry max_{i, j} a_i(j) of a vector sequence a : Fin n → Fin k → ℕ, defined as the supremum of a i j over all pairs (i, j).
-/

/-- The maximum coordinate entry among all vectors in a sequence. -/
def vector_seq_max_entry {n k : ℕ} (a : Fin n → Fin k → ℕ) : ℕ :=
  Finset.univ.sup (fun p : Fin n × Fin k => a p.1 p.2)
