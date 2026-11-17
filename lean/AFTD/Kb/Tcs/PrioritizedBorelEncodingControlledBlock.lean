import AFTD.Prelude
import AFTD.Kb.Tcs.Enc1385Game
import AFTD.Kb.Tcs.Enc1385Replay
import AFTD.Kb.Tcs.Enc1385Follow
import AFTD.Kb.Tcs.FiniteMemoryStrategy
import AFTD.Kb.Tcs.Enc1385FollowActions
import AFTD.Kb.Tcs.PrioritizedBorelEncodingFollowFinal
import AFTD.Kb.Tcs.PrioritizedBorelEncodingFollowProperActions
import AFTD.Kb.Tcs.PrioritizedBorelEncodingActionsEqBlock
import AFTD.Kb.Tcs.PrioritizedBorelEncodingControlledChoicesLegal
import AFTD.Kb.Tcs.PrioritizedBorelFollowActionsReplay
import AFTD.Kb.Tcs.BorelGamePlayer
import AFTD.Kb.Tcs.PrioritizedBorelGame
import AFTD.Kb.Tcs.TreeGameEdge
import AFTD.Kb.Tcs.Enc1385BlockMoves

/-!
# prioritized_borel_encoding_controlled_block

Topic: automata   Node: b1b897fd2ed1

Provenance: helper lemma. Block replay for arXiv:2611.10136, Conjecture 19.

At a position controlled by a player, following that player’s strategy in the phase game for a complete block agrees with replaying the encoded block of some legal original edge from that position, including the resulting phase-game memory and position.
-/

lemma enc1385Assemble {Q M : Type} [Fintype Q] (G : PrioritizedBorelGame Q 3)
    (pl : BorelGamePlayer) (σ : FiniteMemoryStrategy (enc1385Game G) pl M)
    (m : M) (node v : List Bool) (q : Q)
    (hfinal : let st := enc1385Follow G pl σ m node ⟨v,q,[]⟩ (Fintype.card Q)
      let a := σ.choice st.1 st.2.1 st.2.2
      ∃ bits : List Bool, bits.length = Fintype.card Q ∧
        st.2.1 = node ++ bits ∧ st.2.2 = ⟨v,q,bits⟩ ∧
        ∃ e ∈ G.edges, e.source_node = v ∧ e.source_state = q ∧
          bits ++ [a.dir] = enc1385Block e ∧ a.prio = e.prio)
    (hproper : (enc1385FollowActions G pl σ m node ⟨v,q,[]⟩ (Fintype.card Q)).map Prod.fst =
        (enc1385Follow G pl σ m node ⟨v,q,[]⟩ (Fintype.card Q)).2.2.pending ∧
      ∀ a ∈ enc1385FollowActions G pl σ m node ⟨v,q,[]⟩ (Fintype.card Q), a.2 = 0)
    (hlist : ∀ (e : TreeGameEdge Q 3) (xs : List (Bool × Fin 3)) (bit : Bool),
      (∀ a ∈ xs, a.2 = 0) → xs.map Prod.fst ++ [bit] = enc1385Block e →
        xs ++ [(bit,e.prio)] = enc1385BlockMoves e)
    (hreplay : (enc1385FollowActions G pl σ m node ⟨v,q,[]⟩ (Fintype.card Q + 1)).foldl
      (enc1385ReplayStep G pl σ) (m,node,⟨v,q,[]⟩) =
        enc1385Follow G pl σ m node ⟨v,q,[]⟩ (Fintype.card Q + 1)) :
    ∃ e ∈ G.edges, e.source_node = v ∧ e.source_state = q ∧
      enc1385Follow G pl σ m node ⟨v,q,[]⟩ (Fintype.card Q + 1) =
        enc1385Replay G pl σ m node ⟨v,q,[]⟩ e := by
  classical
  let st := enc1385Follow G pl σ m node ⟨v,q,[]⟩ (Fintype.card Q)
  let a := σ.choice st.1 st.2.1 st.2.2
  obtain ⟨bits, hlen, hnode, hstate, e, he, hv, hq, hcode, hprio⟩ := hfinal
  let xs := enc1385FollowActions G pl σ m node ⟨v,q,[]⟩ (Fintype.card Q)
  have hbits : xs.map Prod.fst = bits := by
    have h := hproper.1
    change xs.map Prod.fst = st.2.2.pending at h
    rw [hstate] at h
    exact h
  have hacts : enc1385FollowActions G pl σ m node ⟨v,q,[]⟩ (Fintype.card Q + 1) =
      enc1385BlockMoves e := by
    change xs ++ [(a.dir,a.prio)] = enc1385BlockMoves e
    rw [hprio]
    apply hlist e xs a.dir
    · exact hproper.2
    · rw [hbits]
      exact hcode
  have hr := hreplay
  rw [hacts] at hr
  change enc1385Replay G pl σ m node ⟨v,q,[]⟩ e =
    enc1385Follow G pl σ m node ⟨v,q,[]⟩ (Fintype.card Q + 1) at hr
  exact ⟨e, he, hv, hq, hr.symm⟩

theorem prioritized_borel_encoding_controlled_block {Q M : Type} [Fintype Q]
    (G : PrioritizedBorelGame Q 3) (pl : BorelGamePlayer)
    (σ : FiniteMemoryStrategy (enc1385Game G) pl M)
    (m : M) (node v : List Bool) (q : Q) (hown : G.owner (v,q) = pl) :
    ∃ e ∈ G.edges, e.source_node = v ∧ e.source_state = q ∧
      enc1385Follow G pl σ m node ⟨v,q,[]⟩ (Fintype.card Q + 1) =
        enc1385Replay G pl σ m node ⟨v,q,[]⟩ e := by
  have hfinal := prioritized_borel_encoding_follow_final G pl σ m node v q hown
  have hproper := prioritized_borel_encoding_follow_proper_actions G pl σ m node v q hown
    (Fintype.card Q) (le_refl _)
  have hlegal := prioritized_borel_encoding_controlled_choices_legal G pl σ m node v q hown
  have hreplay := prioritized_borel_follow_actions_replay G pl σ m node ⟨v,q,[]⟩
    (Fintype.card Q + 1) hlegal
  exact enc1385Assemble G pl σ m node v q hfinal hproper
    (fun e xs bit hzero hbits => prioritized_borel_encoding_actions_eq_block e xs bit hzero hbits) hreplay
