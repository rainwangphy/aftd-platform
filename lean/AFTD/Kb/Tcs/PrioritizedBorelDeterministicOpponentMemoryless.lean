import AFTD.Prelude
import AFTD.Kb.Tcs.HasWinningStrategyInMem
import AFTD.Kb.Tcs.FiniteMemoryStrategy
import AFTD.Kb.Tcs.BorelGamePlayer
import AFTD.Kb.Tcs.TreeGameEdge
import AFTD.Kb.Tcs.PrioritizedBorelGame

/-!
# prioritized_borel_deterministic_opponent_memoryless

Topic: automata   Node: b0341e7be3f9

Provenance: helper lemma. Structural step related to arXiv:2611.10136, Conjecture 19.

If every position controlled by Adam in a prioritized Borel game has at most one legal outgoing edge, then one of the players has a winning strategy using one memory state. No finiteness of the state space or Borel determinacy is used.
-/

open Filter
set_option maxHeartbeats 1000000

def op1385Valid {Q : Type} {k : ℕ} (G : PrioritizedBorelGame Q k)
    (π : ℕ → TreeGameEdge Q k) : Prop :=
  (∀ n, π n ∈ G.edges) ∧
  (π 0).source_node = [] ∧ (π 0).source_state = G.init_state ∧
  ∀ n, (π (n+1)).source_node = (π n).source_node ++ [(π n).dir] ∧
       (π (n+1)).source_state = (π n).target_state

def op1385EveWins {Q : Type} {k : ℕ} (G : PrioritizedBorelGame Q k)
    (π : ℕ → TreeGameEdge Q k) : Prop :=
  ∃ p : Fin k, Filter.Frequently (fun n => (π n).prio = p) atTop ∧
    (∀ q : Fin k, p < q → ¬ Filter.Frequently (fun n => (π n).prio = q) atTop) ∧
    (fun n => (π n).dir) ∈ G.winning_sets p

noncomputable def op1385Default {Q : Type} {k : ℕ} (G : PrioritizedBorelGame Q k)
    (v : List Bool) (q : Q) : TreeGameEdge Q k :=
  Classical.choose (G.edges_outgoing v q)

lemma op1385Default_spec {Q : Type} {k : ℕ} (G : PrioritizedBorelGame Q k)
    (v : List Bool) (q : Q) : op1385Default G v q ∈ G.edges ∧
    (op1385Default G v q).source_node = v ∧ (op1385Default G v q).source_state = q :=
  Classical.choose_spec (G.edges_outgoing v q)

noncomputable def op1385Follow {Q : Type} {k : ℕ} (G : PrioritizedBorelGame Q k)
    (target : ℕ → TreeGameEdge Q k) (v : List Bool) (q : Q) : TreeGameEdge Q k := by
  classical
  exact if (target v.length).source_node = v ∧ (target v.length).source_state = q
    then target v.length else op1385Default G v q

lemma op1385Follow_spec {Q : Type} {k : ℕ} (G : PrioritizedBorelGame Q k)
    (target : ℕ → TreeGameEdge Q k) (hvalid : op1385Valid G target)
    (v : List Bool) (q : Q) : op1385Follow G target v q ∈ G.edges ∧
    (op1385Follow G target v q).source_node = v ∧
    (op1385Follow G target v q).source_state = q := by
  classical
  unfold op1385Follow
  split
  · rename_i h
    exact ⟨hvalid.1 _, h.1, h.2⟩
  · exact op1385Default_spec G v q

noncomputable def op1385FollowStrategy {Q : Type} {k : ℕ} (G : PrioritizedBorelGame Q k)
    (target : ℕ → TreeGameEdge Q k) (hvalid : op1385Valid G target) :
    FiniteMemoryStrategy G BorelGamePlayer.Eve Unit where
  init_mem := ()
  update := fun _ _ => ()
  choice := fun _ v q => op1385Follow G target v q
  choice_edge := by
    intro _ v q _
    exact op1385Follow_spec G target hvalid v q

noncomputable def op1385DefaultStrategy {Q : Type} {k : ℕ}
    (G : PrioritizedBorelGame Q k) : FiniteMemoryStrategy G BorelGamePlayer.Adam Unit where
  init_mem := ()
  update := fun _ _ => ()
  choice := fun _ v q => op1385Default G v q
  choice_edge := by
    intro _ v q _
    exact op1385Default_spec G v q

lemma op1385_node_length {Q : Type} {k : ℕ} (G : PrioritizedBorelGame Q k)
    (π : ℕ → TreeGameEdge Q k) (h : op1385Valid G π) :
    ∀ n, (π n).source_node.length = n := by
  intro n
  induction n with
  | zero => simp [h.2.1]
  | succ n ih => rw [(h.2.2.2 n).1]; simp [ih]

lemma op1385_follow_unique {Q : Type} {k : ℕ} (G : PrioritizedBorelGame Q k)
    (target : ℕ → TreeGameEdge Q k) (htarget : op1385Valid G target)
    (hdet : ∀ e ∈ G.edges, ∀ e' ∈ G.edges,
      e.source_node = e'.source_node → e.source_state = e'.source_state →
      G.owner (e.source_node, e.source_state) = BorelGamePlayer.Adam → e = e')
    (π : ℕ → TreeGameEdge Q k) (hπ : op1385Valid G π)
    (hfollow : ∀ n, G.owner ((π n).source_node, (π n).source_state) = BorelGamePlayer.Eve →
      π n = op1385Follow G target (π n).source_node (π n).source_state) : π = target := by
  classical
  funext n
  induction n with
  | zero =>
    have hv : (π 0).source_node = (target 0).source_node := hπ.2.1.trans htarget.2.1.symm
    have hq : (π 0).source_state = (target 0).source_state := hπ.2.2.1.trans htarget.2.2.1.symm
    cases howner : G.owner ((π 0).source_node, (π 0).source_state) with
    | Eve =>
      rw [hfollow 0 howner]
      unfold op1385Follow
      simp [hv, hq, op1385_node_length G target htarget 0]
    | Adam => exact hdet (π 0) (hπ.1 0) (target 0) (htarget.1 0) hv hq howner
  | succ n ih =>
    have hv : (π (n+1)).source_node = (target (n+1)).source_node := by
      rw [(hπ.2.2.2 n).1, (htarget.2.2.2 n).1, ih]
    have hq : (π (n+1)).source_state = (target (n+1)).source_state := by
      rw [(hπ.2.2.2 n).2, (htarget.2.2.2 n).2, ih]
    cases howner : G.owner ((π (n+1)).source_node, (π (n+1)).source_state) with
    | Eve =>
      rw [hfollow (n+1) howner]
      unfold op1385Follow
      simp [hv, hq, op1385_node_length G target htarget (n+1)]
    | Adam => exact hdet (π (n+1)) (hπ.1 (n+1)) (target (n+1)) (htarget.1 (n+1)) hv hq howner

theorem prioritized_borel_deterministic_opponent_memoryless {Q : Type} {k : ℕ}
    (G : PrioritizedBorelGame Q k)
    (hdet : ∀ e ∈ G.edges, ∀ e' ∈ G.edges,
      e.source_node = e'.source_node → e.source_state = e'.source_state →
      G.owner (e.source_node, e.source_state) = BorelGamePlayer.Adam → e = e') :
    HasWinningStrategyInMem G 1 := by
  classical
  by_cases h : ∃ target, op1385Valid G target ∧ op1385EveWins G target
  · obtain ⟨target, ht, hwin⟩ := h
    let σ := op1385FollowStrategy G target ht
    refine ⟨BorelGamePlayer.Eve, Unit, inferInstance, by simp, σ, ?_⟩
    intro π hπ hinit hnext hmem
    have hvalid : op1385Valid G π := ⟨hπ, hinit.1, hinit.2, hnext⟩
    obtain ⟨m, hm0, hmu, hmchoice⟩ := hmem
    have hfollow : ∀ n, G.owner ((π n).source_node, (π n).source_state) = BorelGamePlayer.Eve →
        π n = op1385Follow G target (π n).source_node (π n).source_state := by
      intro n hn
      exact hmchoice n hn
    have heq := op1385_follow_unique G target ht hdet π hvalid hfollow
    subst π
    exact hwin
  · refine ⟨BorelGamePlayer.Adam, Unit, inferInstance, by simp, op1385DefaultStrategy G, ?_⟩
    intro π hπ hinit hnext _ hwin
    exact h ⟨π, ⟨hπ, hinit.1, hinit.2, hnext⟩, hwin⟩
