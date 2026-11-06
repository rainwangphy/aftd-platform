import AFTD.Prelude
import AFTD.Kb.Tcs.F2CubicEdgeCondition
import AFTD.Kb.Tcs.CubicEdge
import AFTD.Kb.Tcs.VectorSeqMaxEntryConstant

/-!
# f2CubicEdgeCondition_witness_zero

Topic: quantum   Node: 1801da52e945

Provenance: helper lemma. step towards op_1254_cubic_hypergraph_fluctuation_mean_zero

Non-vacuity of the fourth-moment predicate: u = 0 and y = 0 always satisfy f2CubicEdgeCondition, so the predicate is not empty for any n.
-/

/-- Sanity witness: the zero tuple satisfies the fourth-moment evenness condition. -/
theorem f2CubicEdgeCondition_witness_zero (n : ℕ) : f2CubicEdgeCondition (0 : Fin n → Fin 2) (fun _ => 0) := by first | exact vector_seq_max_entry_constant | (apply vector_seq_max_entry_constant <;> assumption) | (apply vector_seq_max_entry_constant <;> simp_all) | simpa using vector_seq_max_entry_constant | (simp only [f2CubicEdgeCondition] at *; first | exact vector_seq_max_entry_constant | (apply vector_seq_max_entry_constant <;> assumption) | (apply vector_seq_max_entry_constant <;> simp_all) | simpa using vector_seq_max_entry_constant)
