import AFTD.Prelude
import AFTD.Kb.Tcs.PrioritizedBorelGame
import AFTD.Kb.Tcs.TreeGameEdge
import AFTD.Kb.Tcs.FiniteMemoryStrategy
import AFTD.Kb.Tcs.HasWinningStrategyInMem
import AFTD.Kb.Tcs.BorelGamePlayer

/-!
# prioritized_borel_forward_deterministic_one_state_reduction

Topic: automata   Node: 0d30c2e561c9

Provenance: helper lemma. Forward-deterministic special case of the finite-memory question in arXiv:2611.10136, Conjecture 19.

Fix a prioritized Borel game, any priority count k, and a memory bound b. Suppose that at each node and state, any two legal edges with the same branch direction have the same target state. If every one-state game with k priorities has a winning strategy with at most b memory states, then the given game also has a winning strategy with at most b memory states. The original state type may live in any universe.
-/

noncomputable def op1385NextState {Q : Type*} {k : ℕ} (G : PrioritizedBorelGame Q k)
    (v : List Bool) (q : Q) (b : Bool) : Q := by
  classical
  exact if h : ∃ e ∈ G.edges, e.source_node = v ∧ e.source_state = q ∧ e.dir = b
    then (Classical.choose h).target_state else G.init_state

lemma op1385_next_state_of_edge {Q : Type*} {k : ℕ} (G : PrioritizedBorelGame Q k)
    (hforward : ∀ e ∈ G.edges, ∀ e' ∈ G.edges,
      e.source_node = e'.source_node → e.source_state = e'.source_state →
      e.dir = e'.dir → e.target_state = e'.target_state)
    (e : TreeGameEdge Q k) (he : e ∈ G.edges) :
    op1385NextState G e.source_node e.source_state e.dir = e.target_state := by
  classical
  have hex : ∃ a ∈ G.edges, a.source_node = e.source_node ∧
      a.source_state = e.source_state ∧ a.dir = e.dir := ⟨e, he, rfl, rfl, rfl⟩
  have hs := Classical.choose_spec hex
  have ht := hforward (Classical.choose hex) hs.1 e he hs.2.1 hs.2.2.1 hs.2.2.2
  unfold op1385NextState
  simp only [dif_pos hex, ht]

noncomputable def op1385StateStep {Q : Type*} {k : ℕ} (G : PrioritizedBorelGame Q k)
    (st : List Bool × Q) (b : Bool) : List Bool × Q :=
  (st.1 ++ [b], op1385NextState G st.1 st.2 b)

noncomputable def op1385StatePair {Q : Type*} {k : ℕ} (G : PrioritizedBorelGame Q k)
    (v : List Bool) : List Bool × Q :=
  v.foldl (op1385StateStep G) ([], G.init_state)

lemma op1385_state_pair_node {Q : Type*} {k : ℕ} (G : PrioritizedBorelGame Q k)
    (v : List Bool) : (op1385StatePair G v).1 = v := by
  induction v using List.reverseRecOn with
  | nil => rfl
  | @append_singleton v b ih =>
    unfold op1385StatePair
    rw [List.foldl_append]
    change (op1385StateStep G (op1385StatePair G v) b).1 = v ++ [b]
    simp [op1385StateStep, ih]

noncomputable def op1385NodeState {Q : Type*} {k : ℕ} (G : PrioritizedBorelGame Q k)
    (v : List Bool) : Q := (op1385StatePair G v).2

lemma op1385_node_state_snoc {Q : Type*} {k : ℕ} (G : PrioritizedBorelGame Q k)
    (v : List Bool) (b : Bool) :
    op1385NodeState G (v ++ [b]) = op1385NextState G v (op1385NodeState G v) b := by
  unfold op1385NodeState op1385StatePair
  rw [List.foldl_append]
  change (op1385StateStep G (op1385StatePair G v) b).2 = _
  change op1385NextState G (op1385StatePair G v).1 (op1385StatePair G v).2 b =
    op1385NextState G v (op1385StatePair G v).2 b
  rw [op1385_state_pair_node]

theorem op1385_forward_state_recovered {Q : Type*} {k : ℕ} (G : PrioritizedBorelGame Q k)
    (hforward : ∀ e ∈ G.edges, ∀ e' ∈ G.edges,
      e.source_node = e'.source_node → e.source_state = e'.source_state →
      e.dir = e'.dir → e.target_state = e'.target_state) :
    ∃ s : List Bool → Q, s [] = G.init_state ∧
      ∀ e ∈ G.edges, e.source_state = s e.source_node →
        s (e.source_node ++ [e.dir]) = e.target_state := by
  refine ⟨op1385NodeState G, rfl, ?_⟩
  intro e he hs
  rw [op1385_node_state_snoc, ← hs]
  exact op1385_next_state_of_edge G hforward e he


noncomputable def fwdErase {Q : Type*} {k : ℕ} (e : TreeGameEdge Q k) : TreeGameEdge Unit k where
  source_node := e.source_node
  source_state := ()
  dir := e.dir
  prio := e.prio
  target_state := ()

noncomputable def fwdGame {Q : Type*} {k : ℕ} (G : PrioritizedBorelGame Q k) : PrioritizedBorelGame Unit k where
  owner := fun vq => G.owner (vq.1, op1385NodeState G vq.1)
  init_state := ()
  edges := {e | ∃ a ∈ G.edges, a.source_state = op1385NodeState G a.source_node ∧ fwdErase a = e}
  edges_outgoing := by
    intro v q
    obtain ⟨e, he, hv, hq⟩ := G.edges_outgoing v (op1385NodeState G v)
    refine ⟨fwdErase e, ⟨e, he, ?_, rfl⟩, ?_, ?_⟩
    · simpa [hv] using hq
    · exact hv
    · cases q; rfl
  winning_sets := G.winning_sets
  winning_measurable := G.winning_measurable

noncomputable def fwdBackChoice {Q : Type*} {M : Type} {k : ℕ} (G : PrioritizedBorelGame Q k)
    (pl : BorelGamePlayer) (σ : FiniteMemoryStrategy (fwdGame G) pl M)
    (m : M) (v : List Bool) (q : Q) : TreeGameEdge Q k := by
  classical
  exact if h : ∃ e ∈ G.edges, e.source_node = v ∧ e.source_state = q ∧
      fwdErase e = σ.choice m v () then Classical.choose h
    else Classical.choose (G.edges_outgoing v q)

lemma fwd_back_choice_valid {Q : Type*} {M : Type} {k : ℕ} (G : PrioritizedBorelGame Q k)
    (pl : BorelGamePlayer) (σ : FiniteMemoryStrategy (fwdGame G) pl M)
    (m : M) (v : List Bool) (q : Q) :
    fwdBackChoice G pl σ m v q ∈ G.edges ∧
      (fwdBackChoice G pl σ m v q).source_node = v ∧
      (fwdBackChoice G pl σ m v q).source_state = q := by
  classical
  unfold fwdBackChoice
  split
  · rename_i h
    exact ⟨(Classical.choose_spec h).1, (Classical.choose_spec h).2.1, (Classical.choose_spec h).2.2.1⟩
  · exact Classical.choose_spec (G.edges_outgoing v q)

lemma fwd_back_choice_erases {Q : Type*} {M : Type} {k : ℕ} (G : PrioritizedBorelGame Q k)
    (pl : BorelGamePlayer) (σ : FiniteMemoryStrategy (fwdGame G) pl M)
    (m : M) (v : List Bool) (q : Q) (hq : q = op1385NodeState G v)
    (ho : G.owner (v,q) = pl) : fwdErase (fwdBackChoice G pl σ m v q) = σ.choice m v () := by
  classical
  have hH : (fwdGame G).owner (v,()) = pl := by simpa [fwdGame, ← hq] using ho
  have hs := σ.choice_edge m v () hH
  obtain ⟨e, he, hstate, herase⟩ := hs.1
  have hv : e.source_node = v := by
    simpa [fwdErase, hs.2.1] using congrArg TreeGameEdge.source_node herase
  have heq : ∃ e ∈ G.edges, e.source_node = v ∧ e.source_state = q ∧
      fwdErase e = σ.choice m v () := ⟨e, he, hv, by simpa [hv, hq] using hstate, herase⟩
  unfold fwdBackChoice
  rw [dif_pos heq]
  exact (Classical.choose_spec heq).2.2.2

noncomputable def fwdBackStrategy {Q : Type*} {M : Type} {k : ℕ} (G : PrioritizedBorelGame Q k)
    (pl : BorelGamePlayer) (σ : FiniteMemoryStrategy (fwdGame G) pl M) : FiniteMemoryStrategy G pl M where
  init_mem := σ.init_mem
  update := fun m e => σ.update m (fwdErase e)
  choice := fwdBackChoice G pl σ
  choice_edge := by
    intro m v q _
    exact fwd_back_choice_valid G pl σ m v q

theorem fwd_strategy_transfer {Q : Type*} {k : ℕ} (G : PrioritizedBorelGame Q k)
    (hforward : ∀ e ∈ G.edges, ∀ e' ∈ G.edges,
      e.source_node = e'.source_node → e.source_state = e'.source_state →
      e.dir = e'.dir → e.target_state = e'.target_state)
    (b : ℕ) (hwin : HasWinningStrategyInMem (fwdGame G) b) : HasWinningStrategyInMem G b := by
  obtain ⟨pl, M, inst, hcard, σ, hσ⟩ := hwin
  letI : Fintype M := inst
  let τ := fwdBackStrategy G pl σ
  refine ⟨pl, M, inst, hcard, τ, ?_⟩
  intro π hlegal hinit hnext hfollow
  have hstate : ∀ n, (π n).source_state = op1385NodeState G (π n).source_node := by
    intro n
    induction n with
    | zero =>
      rw [hinit.1, hinit.2]
      rfl
    | succ n ih =>
      rw [(hnext n).1, (hnext n).2, op1385_node_state_snoc, ← ih]
      exact (op1385_next_state_of_edge G hforward (π n) (hlegal n)).symm
  have hHlegal : ∀ n, fwdErase (π n) ∈ (fwdGame G).edges := by
    intro n
    exact ⟨π n, hlegal n, hstate n, rfl⟩
  have hHinit : (fwdErase (π 0)).source_node = [] ∧
      (fwdErase (π 0)).source_state = (fwdGame G).init_state := by
    exact ⟨hinit.1, rfl⟩
  have hHnext : ∀ n, (fwdErase (π (n+1))).source_node =
      (fwdErase (π n)).source_node ++ [(fwdErase (π n)).dir] ∧
      (fwdErase (π (n+1))).source_state = (fwdErase (π n)).target_state := by
    intro n
    exact ⟨(hnext n).1, rfl⟩
  have hHfollow : ∃ mem : ℕ → M, mem 0 = σ.init_mem ∧
      (∀ n, mem (n+1) = σ.update (mem n) (fwdErase (π n))) ∧
      (∀ n, (fwdGame G).owner ((fwdErase (π n)).source_node, (fwdErase (π n)).source_state) = pl →
        fwdErase (π n) = σ.choice (mem n) (fwdErase (π n)).source_node (fwdErase (π n)).source_state) := by
    obtain ⟨mem, hm0, hmupdate, hmchoice⟩ := hfollow
    refine ⟨mem, hm0, hmupdate, ?_⟩
    intro n ho
    have ho' : G.owner ((π n).source_node, (π n).source_state) = pl := by
      simpa [fwdGame, fwdErase, ← hstate n] using ho
    have hc := hmchoice n ho'
    change π n = fwdBackChoice G pl σ (mem n) (π n).source_node (π n).source_state at hc
    exact (congrArg fwdErase hc).trans (fwd_back_choice_erases G pl σ (mem n) (π n).source_node (π n).source_state (hstate n) ho')
  have hw := hσ (fun n => fwdErase (π n)) hHlegal hHinit hHnext hHfollow
  cases pl <;> simpa [fwdGame, fwdErase] using hw

theorem prioritized_borel_forward_deterministic_one_state_reduction {Q : Type*} {k : ℕ}
    (G : PrioritizedBorelGame Q k) (b : ℕ)
    (hforward : ∀ e ∈ G.edges, ∀ e' ∈ G.edges,
      e.source_node = e'.source_node → e.source_state = e'.source_state →
      e.dir = e'.dir → e.target_state = e'.target_state)
    (hone : ∀ H : PrioritizedBorelGame Unit k, HasWinningStrategyInMem H b) :
    HasWinningStrategyInMem G b := by
  exact fwd_strategy_transfer G hforward b (hone (fwdGame G))
