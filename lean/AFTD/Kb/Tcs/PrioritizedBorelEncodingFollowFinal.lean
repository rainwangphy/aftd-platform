import AFTD.Prelude
import AFTD.Kb.Tcs.Enc1385Game
import AFTD.Kb.Tcs.Enc1385Follow
import AFTD.Kb.Tcs.FiniteMemoryStrategy
import AFTD.Kb.Tcs.PrioritizedBorelEncodingFollowProperPrefix
import AFTD.Kb.Tcs.PrioritizedBorelEncodingRealPrefixHasNext
import AFTD.Kb.Tcs.PrioritizedBorelGame
import AFTD.Kb.Tcs.TreeGameEdge
import AFTD.Kb.Tcs.BorelGamePlayer

/-!
# prioritized_borel_encoding_follow_final

Topic: automata   Node: 699b38185982

Provenance: helper lemma. Controlled block simulation for arXiv:2611.10136, Conjecture 19.

At a controlled original position, after the proper-prefix phase steps, the strategy’s final phase choice completes the code of some legal original outgoing edge and carries exactly that edge’s priority.
-/

theorem prioritized_borel_encoding_follow_final {Q M : Type} [Fintype Q] (G : PrioritizedBorelGame Q 3)
    (pl : BorelGamePlayer) (σ : FiniteMemoryStrategy (enc1385Game G) pl M)
    (m : M) (node v : List Bool) (q : Q) (hown : G.owner (v,q) = pl) :
    let st := enc1385Follow G pl σ m node ⟨v,q,[]⟩ (Fintype.card Q)
    let a := σ.choice st.1 st.2.1 st.2.2
    ∃ bits : List Bool, bits.length = Fintype.card Q ∧
      st.2.1 = node ++ bits ∧ st.2.2 = ⟨v,q,bits⟩ ∧
      ∃ e ∈ G.edges, e.source_node = v ∧ e.source_state = q ∧
        bits ++ [a.dir] = enc1385Block e ∧ a.prio = e.prio := by
  classical
  dsimp only
  let st := enc1385Follow G pl σ m node ⟨v,q,[]⟩ (Fintype.card Q)
  let a := σ.choice st.1 st.2.1 st.2.2
  obtain ⟨bits, hlen, hnode, hstate, e, he, hv, hq, hp⟩ :=
    prioritized_borel_encoding_follow_proper_prefix G pl σ m node v q hown (Fintype.card Q) (le_refl _)
  have ho : (enc1385Game G).owner (st.2.1, st.2.2) = pl := by
    change G.owner (st.2.2.origNode, st.2.2.origState) = pl
    simpa [st, hstate] using hown
  have ha := σ.choice_edge st.1 st.2.1 st.2.2 ho
  have hsrc : a.source_state = st.2.2 := ha.2.2
  have hreal_exists : ∃ bit prio, enc1385Real G st.2.2 bit prio := by
    apply prioritized_borel_encoding_real_prefix_has_next G st.2.2 e he
    · simpa [st, hstate] using hv
    · simpa [st, hstate] using hq
    · simpa [st, hstate] using hp
    · simpa [st, hstate, hlen] using (show Fintype.card Q < Fintype.card Q + 1 by omega)
  have ha_allowed : enc1385Allowed G st.2.2 a.dir a.prio := by
    have h : enc1385Allowed G a.source_state a.dir a.prio := ha.1.2
    simpa only [hsrc] using h
  have ha_real : enc1385Real G st.2.2 a.dir a.prio := by
    rcases ha_allowed with hr | ⟨hnone, _, _⟩
    · exact hr
    · exact False.elim (hnone hreal_exists)
  obtain ⟨e', he', hv', hq', hp', hprio⟩ := ha_real
  have hpfx : bits ++ [a.dir] <+: enc1385Block e' := by
    simpa [st, hstate] using hp'
  have heq : bits ++ [a.dir] = enc1385Block e' := by
    apply hpfx.eq_of_length
    simp [hlen, enc1385Block, enc1385StateCode]
  have hpriority : a.prio = e'.prio := by
    simpa [st, hstate, hlen] using hprio
  refine ⟨bits, hlen, hnode, hstate, e', he', ?_, ?_, heq, hpriority⟩
  · simpa [st, hstate] using hv'
  · simpa [st, hstate] using hq'
