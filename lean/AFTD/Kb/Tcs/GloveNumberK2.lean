import AFTD.Prelude
import AFTD.Kb.Tcs.GloveNumber
import AFTD.Kb.Tcs.GloveNumberCompleteGraphUpperBound
import AFTD.Kb.Tcs.Handshake
import AFTD.Kb.Tcs.HandshakeEdge
import AFTD.Kb.Tcs.HasCleanHandshakeSeq
import AFTD.Kb.Tcs.CleanHandshakeSeq

/-!
# glove_number_k2

Topic: combinatorics   Node: 2515aecb29f4

Provenance: formalization of a published result. Source: scout/2610-17602-clean-handshake-sequences.md:348

The glove number of the complete graph $K_2$ is equal to 1.
-/

lemma glove_number_k2_no_zero_gloves :
    ¬ has_clean_handshake_seq (SimpleGraph.completeGraph (Fin 2)) 0 := by
  rintro ⟨seq, -, hcov⟩
  have hedge : (s(0,1) : Sym2 (Fin 2)) ∈ (SimpleGraph.completeGraph (Fin 2)).edgeSet := by
    simp [SimpleGraph.edgeSet]
  obtain ⟨h, -, -⟩ := hcov _ hedge
  cases h with
  | single x a y => exact Fin.elim0 a.1
  | double x a b y => exact Fin.elim0 a.1

/-- The glove number of K_2 is 1. -/
theorem glove_number_k2 : glove_number (SimpleGraph.completeGraph (Fin 2)) = 1 := by
  apply le_antisymm
  · exact glove_number_complete_graph_upper_bound 2 (by norm_num)
  · unfold glove_number
    rw [Nat.one_le_iff_ne_zero]
    intro hzero
    have hne : ({k : ℕ | has_clean_handshake_seq (SimpleGraph.completeGraph (Fin 2)) k}).Nonempty :=
      ⟨1, glove_number_complete_graph_upper_bound_has_clean_seq 1⟩
    have hmem := Nat.sInf_mem hne
    rw [hzero] at hmem
    exact glove_number_k2_no_zero_gloves hmem
