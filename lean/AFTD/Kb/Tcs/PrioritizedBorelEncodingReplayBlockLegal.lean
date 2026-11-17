import AFTD.Prelude
import AFTD.Kb.Tcs.Enc1385Game
import AFTD.Kb.Tcs.Enc1385BlockMoves
import AFTD.Kb.Tcs.Enc1385ReplayEdges
import AFTD.Kb.Tcs.PrioritizedBorelEncodingStateCodeLength
import AFTD.Kb.Tcs.PrioritizedBorelGame
import AFTD.Kb.Tcs.TreeGameEdge

/-!
# prioritized_borel_encoding_replay_block_legal

Topic: automata   Node: ab2c0b11b7c1

Provenance: helper lemma. Opponent-block simulation for arXiv:2611.10136, Conjecture 19.

The complete encoded block of any legal original edge consists of legal phase-game edges when replayed from the matching block boundary.
-/

theorem prioritized_borel_encoding_replay_block_legal {Q : Type} [Fintype Q] (G : PrioritizedBorelGame Q 3) (node v : List Bool) (q : Q) (e : TreeGameEdge Q 3) (he : e ∈ G.edges) (hv : e.source_node = v) (hq : e.source_state = q) : ∀ f ∈ enc1385ReplayEdges G node ⟨v,q,[]⟩ (enc1385BlockMoves e), f ∈ (enc1385Game G).edges := by
  classical
  intro f hf
  set N := Fintype.card Q with hN
  set block : List Bool := enc1385Block e with hblock
  have hblock_len : block.length = N + 1 := by
    simp [hblock, hN, enc1385Block, prioritized_borel_encoding_state_code_length]
  set L : List (Bool × Fin 3) :=
    (List.range (N+1)).map (fun i => (block.getD i false, if i = N then e.prio else 0)) with hLdef
  have hL : enc1385BlockMoves e = L := by
    simp [hLdef, hblock, hN, enc1385BlockMoves]
  have hL_len : L.length = N + 1 := by simp [hLdef]
  rw [hL] at hf
  set s : ℕ → Enc1385State Q := fun m => ⟨v, q, block.take m⟩ with hs
  have hgetL : ∀ m (hm : m < L.length),
      L[m] = ((block.getD m false, if m = N then e.prio else 0) : Bool × Fin 3) := by
    intro m hm
    simp [hLdef, List.getElem_map, List.getElem_range]
  have hcat : ∀ m, m < block.length →
      block.take m ++ [block.getD m false] = block.take (m+1) := by
    intro m hm
    have hgetD : block.getD m false = block[m] := List.getD_eq_getElem block false hm
    rw [hgetD, ← List.concat_eq_append]
    exact List.take_concat_get hm
  have hstep_block : ∀ m, m < N → enc1385Step G (s m) (block.getD m false) = s (m+1) := by
    intro m hmN
    have hmblock : m < block.length := by omega
    have hc := hcat m hmblock
    have hlen : (block.take m ++ [block.getD m false]).length = m + 1 := by
      rw [hc]; simp [List.length_take]; omega
    have hne : (block.take m ++ [block.getD m false]).length ≠ Fintype.card Q + 1 := by
      rw [hlen, ← hN]; omega
    simp only [enc1385Step, hs]
    rw [if_neg hne]
    rw [hc]
  have hstep : ∀ m (hm : m < L.length), m < N →
      enc1385Step G (s m) (L[m]'hm).1 = s (m+1) := by
    intro m hm hmN
    have hml := hgetL m hm
    have hb1 : (L[m]'hm).1 = block.getD m false := by rw [hml]
    rw [hb1]
    exact hstep_block m hmN
  have hreal : ∀ m (hm : m < L.length), enc1385Real G (s m) (L[m]'hm).1 (L[m]'hm).2 := by
    intro m hm
    have hmblock : m < block.length := by omega
    have hml := hgetL m hm
    have hb1 : (L[m]'hm).1 = block.getD m false := by rw [hml]
    have hb2 : (L[m]'hm).2 = (if m = N then e.prio else 0) := by rw [hml]
    have hc := hcat m hmblock
    have hlen : (block.take (m+1)).length = m + 1 := by
      simp [List.length_take]; omega
    refine ⟨e, he, ?_, ?_, ?_, ?_⟩
    · simp only [hs]; exact hv
    · simp only [hs]; exact hq
    · simp only [hs, hb1]
      rw [hc]
      exact List.take_prefix (m+1) (enc1385Block e)
    · simp only [hs, hb1, hb2]
      rw [hc, hlen, ← hN]
      by_cases h : m = N
      · simp [h]
      · simp [h]
  have mem_iff : ∀ E : TreeGameEdge (Enc1385State Q) 3,
      E ∈ (enc1385Game G).edges ↔
        E.target_state = enc1385Step G E.source_state E.dir ∧
          enc1385Allowed G E.source_state E.dir E.prio := by
    intro E
    simp [enc1385Game]
  have key : ∀ d m, m + d = N + 1 → ∀ (nd : List Bool) (g : TreeGameEdge (Enc1385State Q) 3),
      g ∈ enc1385ReplayEdges G nd (s m) (L.drop m) → g ∈ (enc1385Game G).edges := by
    intro d
    induction d with
    | zero =>
      intro m hm nd g hg
      have hdrop : L.drop m = [] := by
        apply List.drop_eq_nil_of_le
        rw [hL_len]; omega
      rw [hdrop, enc1385ReplayEdges.eq_1] at hg
      simp at hg
    | succ d ih =>
      intro m hm nd g hg
      have hmlt : m < L.length := by rw [hL_len]; omega
      have hdrop : L.drop m = L[m] :: L.drop (m+1) := List.drop_eq_getElem_cons hmlt
      rw [hdrop, enc1385ReplayEdges.eq_2] at hg
      rcases List.mem_cons.mp hg with rfl | hg'
      · rw [mem_iff]
        exact ⟨rfl, Or.inl (hreal m hmlt)⟩
      · by_cases hmN : m < N
        · have hsm : enc1385Step G (s m) (L[m]'hmlt).1 = s (m+1) := hstep m hmlt hmN
          rw [hsm] at hg'
          exact ih (m+1) (by omega) (nd ++ [(L[m]'hmlt).1]) g hg'
        · have hnil : L.drop (m+1) = [] := by
            apply List.drop_eq_nil_of_le
            rw [hL_len]; omega
          rw [hnil, enc1385ReplayEdges.eq_1] at hg'
          simp at hg'
  exact key (N+1) 0 (by omega) node f hf
