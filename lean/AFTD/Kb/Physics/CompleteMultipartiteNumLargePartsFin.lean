import AFTD.Prelude
import AFTD.Kb.Physics.CompleteMultipartiteNumLargeParts
import AFTD.Kb.Tcs.VectorSeqMaxEntryConstant

/-!
# complete_multipartite_num_large_parts_fin

Topic: quantum_mechanics   Node: 16e107bd5efe

Provenance: helper lemma. folklore

For any natural number k, the family of k parts each isomorphic to Fin 4 has complete_multipartite_num_large_parts equal to k.
-/

/-- Sanity lemma: a family of k parts each of size 4 has exactly k large parts. -/
theorem complete_multipartite_num_large_parts_fin (k : ℕ) :
    complete_multipartite_num_large_parts (fun _ : Fin k => Fin 4) = k := by first | exact vector_seq_max_entry_constant | (apply vector_seq_max_entry_constant <;> assumption) | (apply vector_seq_max_entry_constant <;> simp_all) | simpa using vector_seq_max_entry_constant | (simp only [complete_multipartite_num_large_parts] at *; first | exact vector_seq_max_entry_constant | (apply vector_seq_max_entry_constant <;> assumption) | (apply vector_seq_max_entry_constant <;> simp_all) | simpa using vector_seq_max_entry_constant)
