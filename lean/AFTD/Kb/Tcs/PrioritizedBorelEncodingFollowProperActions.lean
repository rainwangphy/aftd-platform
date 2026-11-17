import AFTD.Prelude
import AFTD.Kb.Tcs.Enc1385Game
import AFTD.Kb.Tcs.Enc1385Follow
import AFTD.Kb.Tcs.Enc1385FollowActions
import AFTD.Kb.Tcs.PrioritizedBorelEncodingFollowProperPrefix
import AFTD.Kb.Tcs.PrioritizedBorelEncodingRealPrefixHasNext
import AFTD.Kb.Tcs.FiniteMemoryStrategy
import AFTD.Kb.Tcs.TreeGameEdge
import AFTD.Kb.Tcs.PrioritizedBorelGame
import AFTD.Kb.Tcs.BorelGamePlayer
import AFTD.Kb.Tcs.Bit

/-!
# prioritized_borel_encoding_follow_proper_actions

Topic: automata   Node: 2597cc859f1b

Provenance: helper lemma. Controlled block simulation for arXiv:2611.10136, Conjecture 19.

During the proper-prefix steps of a controlled block, the recorded action directions equal the current pending bits and every recorded priority is zero.
-/

lemma enc1385LocalProperActions {Q M : Type} [Fintype Q] (G : PrioritizedBorelGame Q 3)
    (pl : BorelGamePlayer) (σ : FiniteMemoryStrategy (enc1385Game G) pl M)
    (m : M) (node v : List Bool) (q : Q) (hown : G.owner (v,q) = pl) :
    ∀ n, n ≤ Fintype.card Q →
      (enc1385FollowActions G pl σ m node ⟨v,q,[]⟩ n).map Prod.fst =
        (enc1385Follow G pl σ m node ⟨v,q,[]⟩ n).2.2.pending ∧
      ∀ a ∈ enc1385FollowActions G pl σ m node ⟨v,q,[]⟩ n, a.2 = 0 := by
  classical
  intro n
  induction n with
  | zero =>
    intro _
    simp [enc1385FollowActions, enc1385Follow]
  | succ n ih =>
    intro hn
    have hn' : n ≤ Fintype.card Q := by omega
    have hprevious := ih hn'
    obtain ⟨bits, hlen, _, hstate, e, he, hv, hq, hp⟩ :=
      prioritized_borel_encoding_follow_proper_prefix G pl σ m node v q hown n hn'
    let st := enc1385Follow G pl σ m node ⟨v,q,[]⟩ n
    let a := σ.choice st.1 st.2.1 st.2.2
    have ho : (enc1385Game G).owner (st.2.1,st.2.2) = pl := by
      change G.owner (st.2.2.origNode,st.2.2.origState) = pl
      simpa [st, hstate] using hown
    have ha := σ.choice_edge st.1 st.2.1 st.2.2 ho
    have hsrc : a.source_state = st.2.2 := ha.2.2
    have hreal_exists : ∃ bit prio, enc1385Real G st.2.2 bit prio := by
      apply prioritized_borel_encoding_real_prefix_has_next G st.2.2 e he
      · simpa [st, hstate] using hv
      · simpa [st, hstate] using hq
      · simpa [st, hstate] using hp
      · simpa [st, hstate, hlen] using (show n < Fintype.card Q + 1 by omega)
    have ha_allowed : enc1385Allowed G st.2.2 a.dir a.prio := by
      have h : enc1385Allowed G a.source_state a.dir a.prio := ha.1.2
      simpa only [hsrc] using h
    have ha_real : enc1385Real G st.2.2 a.dir a.prio := by
      rcases ha_allowed with hr | ⟨hnone, _, _⟩
      · exact hr
      · exact False.elim (hnone hreal_exists)
    obtain ⟨e', he', hv', hq', hp', hprio⟩ := ha_real
    have hlenne : bits.length ≠ Fintype.card Q := by omega
    have hzero : a.prio = 0 := by
      simpa [st, hstate, hlenne] using hprio
    have htarget : a.target_state = ⟨v,q,bits ++ [a.dir]⟩ := by
      have h : a.target_state = enc1385Step G a.source_state a.dir := ha.1.1
      rw [hsrc, show st.2.2 = ⟨v,q,bits⟩ from hstate] at h
      simpa [enc1385Step, hlenne] using h
    constructor
    · change (enc1385FollowActions G pl σ m node ⟨v,q,[]⟩ n ++ [(a.dir,a.prio)]).map Prod.fst =
        a.target_state.pending
      simp only [List.map_append, List.map_cons, List.map_nil]
      rw [hprevious.1, show st.2.2 = ⟨v,q,bits⟩ from hstate, htarget]
    · change ∀ x ∈ enc1385FollowActions G pl σ m node ⟨v,q,[]⟩ n ++ [(a.dir,a.prio)], x.2 = 0
      intro x hx
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact hprevious.2 x hx
      · exact hzero

theorem prioritized_borel_encoding_follow_proper_actions {Q M : Type} [Fintype Q] (G : PrioritizedBorelGame Q 3) (pl : BorelGamePlayer) (σ : FiniteMemoryStrategy (enc1385Game G) pl M) (m : M) (node v : List Bool) (q : Q) (hown : G.owner (v,q) = pl) (n : ℕ) (hn : n ≤ Fintype.card Q) : (enc1385FollowActions G pl σ m node ⟨v,q,[]⟩ n).map Prod.fst = (enc1385Follow G pl σ m node ⟨v,q,[]⟩ n).2.2.pending ∧ ∀ a ∈ enc1385FollowActions G pl σ m node ⟨v,q,[]⟩ n, a.2 = 0 := by
  exact enc1385LocalProperActions G pl σ m node v q hown n hn
