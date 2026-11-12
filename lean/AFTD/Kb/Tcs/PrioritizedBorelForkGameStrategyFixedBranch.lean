import AFTD.Prelude
import AFTD.Kb.Tcs.PrioritizedBorelForkStrategyFixedBranch
import AFTD.Kb.Tcs.PrioritizedBorelForkAllWinningGame
import AFTD.Kb.Tcs.PrioritizedBorelForkEdge
import AFTD.Kb.Tcs.PrioritizedBorelForkIsLegal
import AFTD.Kb.Tcs.PrioritizedBorelForkExpand
import AFTD.Kb.Tcs.PrioritizedBorelForkRun
import AFTD.Kb.Tcs.PrioritizedBorelForkConsistent
import AFTD.Kb.Tcs.FiniteMemoryStrategy
import AFTD.Kb.Tcs.TreeGameEdge
import AFTD.Kb.Tcs.BorelGamePlayer
import AFTD.Kb.Tcs.PrioritizedBorelGame

/-!
# prioritized_borel_fork_game_strategy_fixed_branch

Topic: automata   Node: e35c8e29af07

Provenance: helper lemma.

For every finite-memory Eve strategy in the all-winning three-state fork game, one infinite visible block sequence and one fixed memory value have arbitrarily large collections of distinct legal finite runs ending at the initial state and memory value, whose controlled moves equal the strategy choices and whose memory is computed by the strategy update.
-/

def in784_encode_from (v : List Bool) : List PrioritizedBorelForkEdge →
    List (TreeGameEdge (Fin 3) 3)
  | [] => []
  | e :: es => ⟨v, e.src, e.dir, e.prio, e.dst⟩ :: in784_encode_from (v ++ [e.dir]) es

theorem in784_encode_from_append (v : List Bool) (xs ys : List PrioritizedBorelForkEdge) :
    in784_encode_from v (xs ++ ys) = in784_encode_from v xs ++
      in784_encode_from (v ++ xs.map PrioritizedBorelForkEdge.dir) ys := by
  induction xs generalizing v with
  | nil => simp [in784_encode_from]
  | cons e es ih => simp [in784_encode_from, ih, List.append_assoc]

theorem in784_encode_from_directions (v : List Bool) (xs : List PrioritizedBorelForkEdge) :
    (in784_encode_from v xs).map TreeGameEdge.dir = xs.map PrioritizedBorelForkEdge.dir := by
  induction xs generalizing v with
  | nil => rfl
  | cons e es ih => simp [in784_encode_from, ih]

def in784_strategy_memory {M : Type}
    (σ : FiniteMemoryStrategy prioritized_borel_fork_all_winning_game BorelGamePlayer.Eve M)
    (es : List PrioritizedBorelForkEdge) : M :=
  (in784_encode_from [] es).foldl σ.update σ.init_mem

theorem in784_strategy_memory_append {M : Type}
    (σ : FiniteMemoryStrategy prioritized_borel_fork_all_winning_game BorelGamePlayer.Eve M)
    (es : List PrioritizedBorelForkEdge) (e : PrioritizedBorelForkEdge) :
    in784_strategy_memory σ (es ++ [e]) =
      σ.update (in784_strategy_memory σ es)
        ⟨es.map PrioritizedBorelForkEdge.dir, e.src, e.dir, e.prio, e.dst⟩ := by
  simp [in784_strategy_memory, in784_encode_from_append, in784_encode_from, List.foldl_append]

def in784_strategy_direction {M : Type}
    (σ : FiniteMemoryStrategy prioritized_borel_fork_all_winning_game BorelGamePlayer.Eve M)
    (es : List PrioritizedBorelForkEdge) : Bool :=
  (σ.choice (in784_strategy_memory σ es) (es.map PrioritizedBorelForkEdge.dir) 2).dir

theorem in784_strategy_obstruction_real_memory {M : Type} [Fintype M]
    (σ : FiniteMemoryStrategy prioritized_borel_fork_all_winning_game BorelGamePlayer.Eve M) :
    ∃ f : ℕ → Bool, ∃ m : M, ∀ d, ∃ n, ∃ S : Finset (List Bool),
      d < S.card ∧
      (∀ h ∈ S,
        prioritized_borel_fork_consistent (in784_strategy_direction σ) []
          (prioritized_borel_fork_expand (List.ofFn (fun i : Fin n => f i)) h) ∧
        in784_strategy_memory σ
          (prioritized_borel_fork_expand (List.ofFn (fun i : Fin n => f i)) h) = m ∧
        PrioritizedBorelForkRun 0
          (prioritized_borel_fork_expand (List.ofFn (fun i : Fin n => f i)) h) 0 ∧
        (prioritized_borel_fork_expand (List.ofFn (fun i : Fin n => f i)) h).map
            PrioritizedBorelForkEdge.dir =
          (List.ofFn (fun i : Fin n => f i)).flatMap (fun b => [false, false, b])) ∧
      (∀ h ∈ S, ∀ k ∈ S,
        prioritized_borel_fork_expand (List.ofFn (fun i : Fin n => f i)) h =
          prioritized_borel_fork_expand (List.ofFn (fun i : Fin n => f i)) k → h = k) := by
  exact prioritized_borel_fork_strategy_fixed_branch
    (in784_strategy_direction σ) (in784_strategy_memory σ)

theorem in784_fork_choice_determined_by_direction {M : Type}
    (σ : FiniteMemoryStrategy prioritized_borel_fork_all_winning_game BorelGamePlayer.Eve M)
    (m : M) (v : List Bool) (e : PrioritizedBorelForkEdge)
    (hlegal : prioritized_borel_fork_is_legal e) (hsrc : e.src = 2)
    (hdir : e.dir = (σ.choice m v 2).dir) :
    (⟨v, e.src, e.dir, e.prio, e.dst⟩ : TreeGameEdge (Fin 3) 3) = σ.choice m v 2 := by
  have howner : prioritized_borel_fork_all_winning_game.owner (v, 2) = BorelGamePlayer.Eve := by
    simp [prioritized_borel_fork_all_winning_game]
  obtain ⟨hc, hv, hs⟩ := σ.choice_edge m v 2 howner
  change prioritized_borel_fork_is_legal
    ⟨(σ.choice m v 2).source_state, (σ.choice m v 2).dir,
      (σ.choice m v 2).target_state, (σ.choice m v 2).prio⟩ at hc
  have hle : e.dst = 0 ∧
      ((e.dir = true ∧ e.prio = 1) ∨ (e.dir = false ∧ e.prio = 2)) := by
    rcases hlegal with a | a | a | a <;> simp_all [prioritized_borel_fork_is_legal]
  have hlc : (σ.choice m v 2).target_state = 0 ∧
      (((σ.choice m v 2).dir = true ∧ (σ.choice m v 2).prio = 1) ∨
       ((σ.choice m v 2).dir = false ∧ (σ.choice m v 2).prio = 2)) := by
    rcases hc with a | a | a | a <;> simp_all [prioritized_borel_fork_is_legal]
  obtain ⟨hedst, hecase⟩ := hle
  obtain ⟨hcdst, hccase⟩ := hlc
  have hprio : e.prio = (σ.choice m v 2).prio := by
    rcases hecase with he | he <;> rcases hccase with hc | hc <;> simp_all
  cases e
  cases he : σ.choice m v 2
  simp_all

def in784_actual_consistent {M : Type}
    (σ : FiniteMemoryStrategy prioritized_borel_fork_all_winning_game BorelGamePlayer.Eve M) :
    List PrioritizedBorelForkEdge → List PrioritizedBorelForkEdge → Prop
  | _, [] => True
  | pre, e :: es =>
      (e.src = 2 →
        (⟨pre.map PrioritizedBorelForkEdge.dir, e.src, e.dir, e.prio, e.dst⟩ :
          TreeGameEdge (Fin 3) 3) =
          σ.choice (in784_strategy_memory σ pre)
            (pre.map PrioritizedBorelForkEdge.dir) 2) ∧
      in784_actual_consistent σ (pre ++ [e]) es

theorem in784_direction_consistency_is_actual {M : Type}
    (σ : FiniteMemoryStrategy prioritized_borel_fork_all_winning_game BorelGamePlayer.Eve M)
    (pre es : List PrioritizedBorelForkEdge)
    (hlegal : ∀ e ∈ es, prioritized_borel_fork_is_legal e)
    (hc : prioritized_borel_fork_consistent (in784_strategy_direction σ) pre es) :
    in784_actual_consistent σ pre es := by
  induction es generalizing pre with
  | nil => trivial
  | cons e es ih =>
      change (e.src = 2 → e.dir = in784_strategy_direction σ pre) ∧
        prioritized_borel_fork_consistent (in784_strategy_direction σ) (pre ++ [e]) es at hc
      change (e.src = 2 → _ ) ∧ in784_actual_consistent σ (pre ++ [e]) es
      refine ⟨?_, ih (pre ++ [e]) ?_ hc.2⟩
      · intro hs
        apply in784_fork_choice_determined_by_direction σ (in784_strategy_memory σ pre)
          (pre.map PrioritizedBorelForkEdge.dir) e (hlegal e (by simp)) hs
        exact hc.1 hs
      · intro e' he'
        exact hlegal e' (by simp [he'])

theorem in784_fork_run_edges_legal {q r : Fin 3} {es : List PrioritizedBorelForkEdge}
    (hr : PrioritizedBorelForkRun q es r) : ∀ e ∈ es, prioritized_borel_fork_is_legal e := by
  induction hr with
  | nil => simp
  | cons hlegal hsrc hrun ih =>
      intro e he
      simp only [List.mem_cons] at he
      rcases he with rfl | he
      · exact hlegal
      · exact ih e he

theorem prioritized_borel_fork_game_strategy_fixed_branch {M : Type} [Fintype M]
    (σ : FiniteMemoryStrategy prioritized_borel_fork_all_winning_game BorelGamePlayer.Eve M) :
    ∃ f : ℕ → Bool, ∃ m : M, ∀ d, ∃ n, ∃ S : Finset (List Bool),
      d < S.card ∧
      (∀ h ∈ S,
        in784_actual_consistent σ []
          (prioritized_borel_fork_expand (List.ofFn (fun i : Fin n => f i)) h) ∧
        in784_strategy_memory σ
          (prioritized_borel_fork_expand (List.ofFn (fun i : Fin n => f i)) h) = m ∧
        PrioritizedBorelForkRun 0
          (prioritized_borel_fork_expand (List.ofFn (fun i : Fin n => f i)) h) 0 ∧
        (prioritized_borel_fork_expand (List.ofFn (fun i : Fin n => f i)) h).map
            PrioritizedBorelForkEdge.dir =
          (List.ofFn (fun i : Fin n => f i)).flatMap (fun b => [false, false, b])) ∧
      (∀ h ∈ S, ∀ k ∈ S,
        prioritized_borel_fork_expand (List.ofFn (fun i : Fin n => f i)) h =
          prioritized_borel_fork_expand (List.ofFn (fun i : Fin n => f i)) k → h = k) := by
  obtain ⟨f, m, hf⟩ := in784_strategy_obstruction_real_memory σ
  refine ⟨f, m, ?_⟩
  intro d
  obtain ⟨n, S, hs, hall, hinj⟩ := hf d
  refine ⟨n, S, hs, ?_, hinj⟩
  intro h hh
  obtain ⟨hc, hm, hr, hd⟩ := hall h hh
  exact ⟨in784_direction_consistency_is_actual σ [] _ (in784_fork_run_edges_legal hr) hc,
    hm, hr, hd⟩
