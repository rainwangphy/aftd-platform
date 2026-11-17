import AFTD.Prelude
import AFTD.Kb.Tcs.Enc1385Game
import AFTD.Kb.Tcs.Enc1385Replay
import AFTD.Kb.Tcs.Enc1385BlockMoves
import AFTD.Kb.Tcs.PrioritizedBorelEncodingStateCodeLength
import AFTD.Kb.Tcs.PrioritizedBorelEncodingDecodeState
import AFTD.Kb.Tcs.PrioritizedBorelGame
import AFTD.Kb.Tcs.BorelGamePlayer
import AFTD.Kb.Tcs.FiniteMemoryStrategy
import AFTD.Kb.Tcs.TreeGameEdge

/-!
# prioritized_borel_encoding_replay_boundary

Topic: automata   Node: bccadeecc4a7

Provenance: helper lemma. Block replay for arXiv:2611.10136, Conjecture 19.

Replaying an edge block from a block boundary appends its encoded bits to the phase-game node and ends at the original child node and target state with an empty pending prefix, regardless of the strategy's memory updates.
-/

set_option maxHeartbeats 800000 in
/-- After replaying the first `n` phase moves of an edge block from a state with empty
pending prefix, the node has gained exactly the first `n` block bits and the phase state
stores exactly those bits as its pending prefix. -/
private theorem prioritized_borel_encoding_replay_boundary_aux {Q M : Type} [Fintype Q]
    (G : PrioritizedBorelGame Q 3) (pl : BorelGamePlayer)
    (σ : FiniteMemoryStrategy (enc1385Game G) pl M) (m : M) (node v : List Bool) (q : Q)
    (e : TreeGameEdge Q 3) :
    ∀ n : ℕ, n ≤ Fintype.card Q →
    ∃ m' : M, List.foldl (enc1385ReplayStep G pl σ) (m, node, (⟨v, q, []⟩ : Enc1385State Q))
        ((enc1385BlockMoves e).take n)
      = (m', node ++ (enc1385Block e).take n, (⟨v, q, (enc1385Block e).take n⟩ : Enc1385State Q)) := by
  intro n
  induction n with
  | zero => intro _; exact ⟨m, by simp⟩
  | succ n ih =>
    intro hn
    obtain ⟨m', hm'⟩ := ih (by omega)
    have hcode := prioritized_borel_encoding_state_code_length (Q := Q) e.target_state
    have hlenB : (enc1385Block e).length = Fintype.card Q + 1 := by
      simp [enc1385Block, hcode]
    have hlenm : (enc1385BlockMoves e).length = Fintype.card Q + 1 := by
      simp [enc1385BlockMoves]
    have hlt : n < (enc1385BlockMoves e).length := by rw [hlenm]; omega
    have hnltB : n < (enc1385Block e).length := by rw [hlenB]; omega
    have hbit : (enc1385BlockMoves e)[n]
        = ((enc1385Block e).getD n false, (if n = Fintype.card Q then e.prio else 0)) := by
      simp [enc1385BlockMoves, List.getElem_map, List.getElem_range]
    have htake : (enc1385Block e).take n ++ [(enc1385Block e).getD n false]
        = (enc1385Block e).take (n + 1) := by
      rw [List.getD_eq_getElem _ _ hnltB, List.take_concat_get' _ _ hnltB]
    have hstep : enc1385Step G (⟨v, q, (enc1385Block e).take n⟩ : Enc1385State Q)
        ((enc1385Block e).getD n false) = ⟨v, q, (enc1385Block e).take (n + 1)⟩ := by
      have hlen : ¬ ((enc1385Block e).take n
          ++ [(enc1385Block e).getD n false]).length = Fintype.card Q + 1 := by
        rw [List.length_append, List.length_take, hlenB, List.length_singleton]
        have hmin : min n (Fintype.card Q + 1) = n := Nat.min_eq_left (by omega)
        omega
      simp only [enc1385Step]
      rw [if_neg hlen, htake]
    have h1 : (enc1385BlockMoves e).take (n + 1)
        = (enc1385BlockMoves e).take n ++ [(enc1385BlockMoves e)[n]] :=
      (List.take_concat_get' (enc1385BlockMoves e) n hlt).symm
    rw [h1, List.foldl_append, hm']
    simp only [List.foldl_cons, List.foldl_nil, enc1385ReplayStep, hbit, hstep]
    exact ⟨_, by rw [List.append_assoc, htake]⟩

theorem prioritized_borel_encoding_replay_boundary {Q M : Type} [Fintype Q] (G : PrioritizedBorelGame Q 3) (pl : BorelGamePlayer) (σ : FiniteMemoryStrategy (enc1385Game G) pl M) (m : M) (node v : List Bool) (q : Q) (e : TreeGameEdge Q 3) : (enc1385Replay G pl σ m node ⟨v,q,[]⟩ e).2.1 = node ++ enc1385Block e ∧ (enc1385Replay G pl σ m node ⟨v,q,[]⟩ e).2.2 = ⟨v ++ [e.dir], e.target_state, []⟩ := by
  obtain ⟨m', hm'⟩ :=
    prioritized_borel_encoding_replay_boundary_aux G pl σ m node v q e (Fintype.card Q) le_rfl
  have hcode := prioritized_borel_encoding_state_code_length (Q := Q) e.target_state
  have hlenB : (enc1385Block e).length = Fintype.card Q + 1 := by
    simp [enc1385Block, hcode]
  have hlenm : (enc1385BlockMoves e).length = Fintype.card Q + 1 := by simp [enc1385BlockMoves]
  have hlt : Fintype.card Q < (enc1385BlockMoves e).length := by rw [hlenm]; omega
  have hnltB : Fintype.card Q < (enc1385Block e).length := by rw [hlenB]; omega
  have hbit : (enc1385BlockMoves e)[Fintype.card Q]
      = ((enc1385Block e).getD (Fintype.card Q) false, e.prio) := by
    simp [enc1385BlockMoves, List.getElem_map, List.getElem_range]
  have htake : (enc1385Block e).take (Fintype.card Q)
        ++ [(enc1385Block e).getD (Fintype.card Q) false] = enc1385Block e := by
    rw [List.getD_eq_getElem _ _ hnltB, List.take_concat_get' _ _ hnltB,
      List.take_of_length_le (by rw [hlenB])]
  have hhead : (enc1385Block e).headD false = e.dir := by simp [enc1385Block]
  have htail : (enc1385Block e).tail = enc1385StateCode e.target_state := by
    simp [enc1385Block]
  have hstep : enc1385Step G (⟨v, q, (enc1385Block e).take (Fintype.card Q)⟩ : Enc1385State Q)
      ((enc1385Block e).getD (Fintype.card Q) false) = ⟨v ++ [e.dir], e.target_state, []⟩ := by
    have hlen : ((enc1385Block e).take (Fintype.card Q)
        ++ [(enc1385Block e).getD (Fintype.card Q) false]).length = Fintype.card Q + 1 := by
      rw [htake, hlenB]
    simp only [enc1385Step]
    rw [if_pos hlen, htake, hhead, htail, prioritized_borel_encoding_decode_state]
  have h1 : enc1385BlockMoves e
      = (enc1385BlockMoves e).take (Fintype.card Q) ++ [(enc1385BlockMoves e)[Fintype.card Q]] := by
    rw [List.take_concat_get' (enc1385BlockMoves e) (Fintype.card Q) hlt,
      List.take_of_length_le (by rw [hlenm])]
  unfold enc1385Replay
  rw [h1, List.foldl_append, hm']
  simp only [List.foldl_cons, List.foldl_nil]
  rw [hbit]
  unfold enc1385ReplayStep
  rw [hstep]
  exact ⟨by rw [List.append_assoc, htake], rfl⟩
