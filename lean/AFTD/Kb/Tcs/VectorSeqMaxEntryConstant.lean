import AFTD.Prelude
import AFTD.Kb.Tcs.VectorSeqMaxEntry

/-!
# vector_seq_max_entry_constant

Topic: combinatorics   Node: ae67ced48fff

Provenance: helper lemma. arXiv:2610.26970 Def 1.1

For positive integers n and k, the maximum entry of a constant sequence of vectors equal to c is c.
-/

/-- The maximum entry of a constant vector sequence equals the constant value. -/
theorem vector_seq_max_entry_constant {n k : ℕ} (hn : 0 < n) (hk : 0 < k) (c : ℕ) :
    vector_seq_max_entry (fun (_ : Fin n) (_ : Fin k) => c) = c := by
  unfold vector_seq_max_entry
  exact Finset.sup_const ⟨(⟨0, hn⟩, ⟨0, hk⟩), Finset.mem_univ _⟩ c
