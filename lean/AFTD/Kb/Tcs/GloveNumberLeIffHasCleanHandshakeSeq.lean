import AFTD.Prelude
import AFTD.Kb.Tcs.HasCleanHandshakeSeqMono
import AFTD.Kb.Tcs.GloveNumber
import AFTD.Kb.Tcs.HasCleanHandshakeSeq

/-!
# glove_number_le_iff_has_clean_handshake_seq

Topic: combinatorics   Node: 5ce95b6a1560

Provenance: helper lemma. step towards glove_number_complete_graph_open_problem

If some number of gloves suffices for a graph $G$, then for every $k$ the glove number of $G$ is at most $k$ if and only if $G$ has a clean handshake sequence with $k$ gloves.
-/

/-- For a graph some number of gloves suffices for, having at most `k` gloves is the same as having a `k`-glove covering sequence. -/
theorem glove_number_le_iff_has_clean_handshake_seq {V : Type*} (G : SimpleGraph V)
    (hne : ∃ j, has_clean_handshake_seq G j) (k : ℕ) :
    glove_number G ≤ k ↔ has_clean_handshake_seq G k := by
  have hS : {j : ℕ | has_clean_handshake_seq G j} = Set.Ici (glove_number G) := by
    show {j : ℕ | has_clean_handshake_seq G j} =
      Set.Ici (sInf {j : ℕ | has_clean_handshake_seq G j})
    exact Nat.eq_Ici_of_nonempty_of_upward_closed hne
      (fun k₁ k₂ hkk hk => has_clean_handshake_seq_mono G hkk hk)
  rw [← Set.mem_Ici, ← hS]
  rfl
