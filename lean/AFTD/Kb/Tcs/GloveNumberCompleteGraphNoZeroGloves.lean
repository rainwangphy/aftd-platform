import AFTD.Prelude
import AFTD.Kb.Tcs.HasCleanHandshakeSeq
import AFTD.Kb.Tcs.CleanHandshakeSeq
import AFTD.Kb.Tcs.HandshakeEdge
import AFTD.Kb.Tcs.Handshake

/-!
# glove_number_complete_graph_no_zero_gloves

Topic: combinatorics   Node: 4f896866495f

Provenance: helper lemma. arXiv:2610.17602 Section 2 (Clean handshake sequences)

For any integer $n \ge 2$, there is no clean handshake sequence with zero gloves covering all edges of the complete graph $K_n$.
-/

/-- For n ≥ 2, there is no clean handshake sequence for K_n using zero gloves. -/
theorem glove_number_complete_graph_no_zero_gloves (n : ℕ) (hn : 2 ≤ n) :
    ¬ has_clean_handshake_seq (SimpleGraph.completeGraph (Fin n)) 0 := by
  rintro ⟨seq, -, hcov⟩
  have hedge : s((⟨0, by omega⟩ : Fin n), (⟨1, by omega⟩ : Fin n)) ∈
      (SimpleGraph.completeGraph (Fin n)).edgeSet := by
    rw [SimpleGraph.mem_edgeSet]
    simp only [SimpleGraph.completeGraph, SimpleGraph.top_adj, ne_eq]
    intro hne
    have := Fin.mk.inj_iff.mp hne
    omega
  obtain ⟨h, hmem, -⟩ := hcov _ hedge
  cases h with
  | single x a y => exact Fin.elim0 a.1
  | double x a b y => exact Fin.elim0 a.1
