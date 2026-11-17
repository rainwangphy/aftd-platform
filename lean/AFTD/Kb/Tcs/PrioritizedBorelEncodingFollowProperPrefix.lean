import AFTD.Prelude
import AFTD.Kb.Tcs.Enc1385Game
import AFTD.Kb.Tcs.Enc1385Follow
import AFTD.Kb.Tcs.FiniteMemoryStrategy
import AFTD.Kb.Tcs.PrioritizedBorelEncodingRealPrefixHasNext
import AFTD.Kb.Tcs.TreeGameEdge
import AFTD.Kb.Tcs.PrioritizedBorelGame
import AFTD.Kb.Tcs.BorelGamePlayer

/-!
# prioritized_borel_encoding_follow_proper_prefix

Topic: automata   Node: 4a23739e4e11

Provenance: helper lemma. Controlled block simulation for arXiv:2611.10136, Conjecture 19.

At an original position controlled by the given player, after any number of phase-game strategy steps up to the number of states, the original node and state are unchanged; the phase holds the selected bit prefix, the encoded node has that prefix appended, and the prefix extends to the code of a legal original edge.
-/

theorem prioritized_borel_encoding_follow_proper_prefix {Q M : Type} [Fintype Q] (G : PrioritizedBorelGame Q 3)
    (pl : BorelGamePlayer) (σ : FiniteMemoryStrategy (enc1385Game G) pl M)
    (m : M) (node v : List Bool) (q : Q) (hown : G.owner (v,q) = pl) :
    ∀ n, n ≤ Fintype.card Q →
      ∃ bits : List Bool, bits.length = n ∧
        (enc1385Follow G pl σ m node ⟨v,q,[]⟩ n).2.1 = node ++ bits ∧
        (enc1385Follow G pl σ m node ⟨v,q,[]⟩ n).2.2 = ⟨v,q,bits⟩ ∧
        ∃ e ∈ G.edges, e.source_node = v ∧ e.source_state = q ∧ bits <+: enc1385Block e := by
  classical
  intro n
  induction n with
  | zero =>
    intro _
    obtain ⟨e, he, hv, hq⟩ := G.edges_outgoing v q
    refine ⟨[], rfl, ?_, rfl, e, he, hv, hq, ?_⟩
    · simp [enc1385Follow]
    · exact List.nil_prefix
  | succ n ih =>
    intro hn
    have hn' : n ≤ Fintype.card Q := by omega
    obtain ⟨bits, hlen, hnode, hstate, e, he, hv, hq, hp⟩ := ih hn'
    let st := enc1385Follow G pl σ m node ⟨v,q,[]⟩ n
    let a := σ.choice st.1 st.2.1 st.2.2
    have ho : (enc1385Game G).owner (st.2.1, st.2.2) = pl := by
      change G.owner (st.2.2.origNode, st.2.2.origState) = pl
      simpa [st, hstate] using hown
    have ha := σ.choice_edge st.1 st.2.1 st.2.2 ho
    have hreal_exists : ∃ bit prio, enc1385Real G st.2.2 bit prio := by
      apply prioritized_borel_encoding_real_prefix_has_next G st.2.2 e he
      · simpa [st, hstate] using hv
      · simpa [st, hstate] using hq
      · simpa [st, hstate] using hp
      · simpa [st, hstate, hlen] using (show n < Fintype.card Q + 1 by omega)
    have hsrc : a.source_state = st.2.2 := ha.2.2
    have ha_allowed : enc1385Allowed G st.2.2 a.dir a.prio := by
      have h : enc1385Allowed G a.source_state a.dir a.prio := ha.1.2
      simpa only [hsrc] using h
    have ha_real : enc1385Real G st.2.2 a.dir a.prio := by
      rcases ha_allowed with hr | ⟨hnone, _, _⟩
      · exact hr
      · exact False.elim (hnone hreal_exists)
    obtain ⟨e', he', hv', hq', hp', _⟩ := ha_real
    have hne : (bits ++ [a.dir]).length ≠ Fintype.card Q + 1 := by
      simp [hlen]
      omega
    have htarget : a.target_state = ⟨v,q,bits ++ [a.dir]⟩ := by
      have h : a.target_state = enc1385Step G a.source_state a.dir := ha.1.1
      rw [hsrc, show st.2.2 = ⟨v,q,bits⟩ from hstate] at h
      have hlenne : bits.length ≠ Fintype.card Q := by omega
      simpa [enc1385Step, hlenne] using h
    refine ⟨bits ++ [a.dir], by simp [hlen], ?_, ?_, e', he', ?_, ?_, ?_⟩
    · change st.2.1 ++ [a.dir] = node ++ (bits ++ [a.dir])
      rw [hnode, List.append_assoc]
    · change a.target_state = ⟨v,q,bits ++ [a.dir]⟩
      exact htarget
    · simpa [st, hstate] using hv'
    · simpa [st, hstate] using hq'
    · simpa [st, hstate] using hp'
