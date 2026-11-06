import AFTD.Prelude
import AFTD.Kb.Optimization.IsSubmodularBounded
import AFTD.Kb.Tcs.VectorSeqMaxEntryConstant

/-!
# op_932_constant_fn_submodular

Topic: submodular   Node: 3fa7b709d1dd

Provenance: helper lemma. arXiv:2611.02374 Def. 2.1

For any n, k, and value v, the constant function f(x) = v on {0, 1}^n is submodular.
-/

/-- Constant functions on the hypercube with bounded range are submodular. -/
theorem op_932_constant_fn_submodular (n k : ℕ) (v : Fin (k + 1)) :
    is_submodular_bounded n k (fun _ => v) := by first | exact vector_seq_max_entry_constant | (apply vector_seq_max_entry_constant <;> assumption) | (apply vector_seq_max_entry_constant <;> simp_all) | simpa using vector_seq_max_entry_constant | (simp only [is_submodular_bounded] at *; first | exact vector_seq_max_entry_constant | (apply vector_seq_max_entry_constant <;> assumption) | (apply vector_seq_max_entry_constant <;> simp_all) | simpa using vector_seq_max_entry_constant)
