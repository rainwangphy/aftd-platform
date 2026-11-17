import AFTD.Prelude
import AFTD.Kb.Tcs.Enc1385Game
import AFTD.Kb.Tcs.Enc1385Replay
import AFTD.Kb.Tcs.Enc1385Follow
import AFTD.Kb.Tcs.Enc1385FollowActions
import AFTD.Kb.Tcs.TreeGameEdge
import AFTD.Kb.Tcs.FiniteMemoryStrategy
import AFTD.Kb.Tcs.BorelGamePlayer
import AFTD.Kb.Tcs.PrioritizedBorelGame

/-!
# prioritized_borel_follow_actions_replay

Topic: automata   Node: dd720b453183

Provenance: helper lemma. Block replay for arXiv:2611.10136, Conjecture 19.

If each of the first n selected phase-game moves is legal at its selected position, replaying their direction and priority actions produces the same final memory and position as following the strategy.
-/

lemma enc1385LocalFollowReplay {Q M : Type} [Fintype Q] (G : PrioritizedBorelGame Q 3)
    (pl : BorelGamePlayer) (σ : FiniteMemoryStrategy (enc1385Game G) pl M)
    (m : M) (node : List Bool) (s : Enc1385State Q) :
    ∀ n, (∀ i < n, let st := enc1385Follow G pl σ m node s i
      let e := σ.choice st.1 st.2.1 st.2.2
      e ∈ (enc1385Game G).edges ∧ e.source_node = st.2.1 ∧ e.source_state = st.2.2) →
      (enc1385FollowActions G pl σ m node s n).foldl (enc1385ReplayStep G pl σ) (m,node,s) =
        enc1385Follow G pl σ m node s n := by
  intro n
  induction n with
  | zero =>
    intro _
    rfl
  | succ n ih =>
    intro hlegal
    have hlegaln : ∀ i < n, let st := enc1385Follow G pl σ m node s i
        let e := σ.choice st.1 st.2.1 st.2.2
        e ∈ (enc1385Game G).edges ∧ e.source_node = st.2.1 ∧ e.source_state = st.2.2 := by
      intro i hi
      exact hlegal i (by omega)
    let st := enc1385Follow G pl σ m node s n
    let e := σ.choice st.1 st.2.1 st.2.2
    have hv : e ∈ (enc1385Game G).edges ∧ e.source_node = st.2.1 ∧ e.source_state = st.2.2 :=
      hlegal n (by omega)
    have ht : e.target_state = enc1385Step G e.source_state e.dir := hv.1.1
    have heq : (⟨st.2.1, st.2.2, e.dir, e.prio, enc1385Step G st.2.2 e.dir⟩ :
        TreeGameEdge (Enc1385State Q) 3) = e := by
      rw [← hv.2.1, ← hv.2.2, ← ht]
    have ht' : enc1385Step G st.2.2 e.dir = e.target_state := by
      rw [← hv.2.2]
      exact ht.symm
    simp only [enc1385FollowActions, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [ih hlegaln]
    change enc1385ReplayStep G pl σ st (e.dir,e.prio) =
      (σ.update st.1 e, st.2.1 ++ [e.dir], e.target_state)
    simp only [enc1385ReplayStep]
    rw [heq, ht']

theorem prioritized_borel_follow_actions_replay {Q M : Type} [Fintype Q] (G : PrioritizedBorelGame Q 3) (pl : BorelGamePlayer) (σ : FiniteMemoryStrategy (enc1385Game G) pl M) (m : M) (node : List Bool) (s : Enc1385State Q) (n : ℕ) (hlegal : ∀ i < n, let st := enc1385Follow G pl σ m node s i; let e := σ.choice st.1 st.2.1 st.2.2; e ∈ (enc1385Game G).edges ∧ e.source_node = st.2.1 ∧ e.source_state = st.2.2) : (enc1385FollowActions G pl σ m node s n).foldl (enc1385ReplayStep G pl σ) (m,node,s) = enc1385Follow G pl σ m node s n := by
  exact enc1385LocalFollowReplay G pl σ m node s n hlegal
