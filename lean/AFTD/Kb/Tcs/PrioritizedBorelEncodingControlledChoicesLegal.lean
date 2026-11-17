import AFTD.Prelude
import AFTD.Kb.Tcs.Enc1385Game
import AFTD.Kb.Tcs.Enc1385Follow
import AFTD.Kb.Tcs.FiniteMemoryStrategy
import AFTD.Kb.Tcs.PrioritizedBorelEncodingFollowProperPrefix
import AFTD.Kb.Tcs.TreeGameEdge
import AFTD.Kb.Tcs.BorelGamePlayer
import AFTD.Kb.Tcs.PrioritizedBorelGame

/-!
# prioritized_borel_encoding_controlled_choices_legal

Topic: automata   Node: f6b5bf0695bb

Provenance: helper lemma. Controlled block simulation for arXiv:2611.10136, Conjecture 19.

At a controlled original position, every strategy choice within one encoded block is a legal phase-game edge from the selected phase-game position.
-/

theorem prioritized_borel_encoding_controlled_choices_legal {Q M : Type} [Fintype Q] (G : PrioritizedBorelGame Q 3)
    (pl : BorelGamePlayer) (σ : FiniteMemoryStrategy (enc1385Game G) pl M)
    (m : M) (node v : List Bool) (q : Q) (hown : G.owner (v,q) = pl) :
    ∀ i < Fintype.card Q + 1,
      let st := enc1385Follow G pl σ m node ⟨v,q,[]⟩ i
      let e := σ.choice st.1 st.2.1 st.2.2
      e ∈ (enc1385Game G).edges ∧ e.source_node = st.2.1 ∧ e.source_state = st.2.2 := by
  intro i hi
  have hi' : i ≤ Fintype.card Q := by omega
  obtain ⟨bits, _, _, hstate, _⟩ :=
    prioritized_borel_encoding_follow_proper_prefix G pl σ m node v q hown i hi'
  let st := enc1385Follow G pl σ m node ⟨v,q,[]⟩ i
  have ho : (enc1385Game G).owner (st.2.1,st.2.2) = pl := by
    change G.owner (st.2.2.origNode,st.2.2.origState) = pl
    simpa [st, hstate] using hown
  exact σ.choice_edge st.1 st.2.1 st.2.2 ho
