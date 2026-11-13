import AFTD.Prelude
import AFTD.Kb.Tcs.PrioritizedBorelGame
import AFTD.Kb.Tcs.FiniteMemoryStrategy
import AFTD.Kb.Tcs.PrioritizedBorelStrategyWins
import AFTD.Kb.Tcs.TreeGameEdge
import AFTD.Kb.Tcs.BorelGamePlayer
import AFTD.Kb.Tcs.PrioritizedBorelReverseStateHistoriesUnique

/-!
# prioritized_borel_reverse_edge_deterministic_positional

Topic: automata   Node: c5d87499b006

Provenance: original. Related work: Reverse edge-history reconstruction related to arXiv:2611.10136, Conjecture 19.

If the current node and target state uniquely determine the previous state, and the node, source state, direction and target state uniquely determine each edge priority, then any winning strategy can be replaced by a positional one. The state space and memory type may be arbitrary.
-/

/-- A legal play prefix: all edges are in the arena, it starts at the empty node, and successive edges are linked by the tree structure. -/
structure prioritized_borel_reverse_edge_deterministic_positional_legal
    {Q : Type} {k : ℕ} (G : PrioritizedBorelGame Q k) (p : ℕ → TreeGameEdge Q k) : Prop where
  edge : ∀ n, p n ∈ G.edges
  node_zero : (p 0).source_node = []
  step : ∀ n, (p (n+1)).source_node = (p n).source_node ++ [(p n).dir] ∧
    (p (n+1)).source_state = (p n).target_state

/-- The node of step `n` of a legal play has length `n`. -/
lemma prioritized_borel_reverse_edge_deterministic_positional_node_length
    {Q : Type} {k : ℕ} {G : PrioritizedBorelGame Q k} {p : ℕ → TreeGameEdge Q k}
    (hp : prioritized_borel_reverse_edge_deterministic_positional_legal G p) :
    ∀ n, (p n).source_node.length = n := by
  intro n
  induction n with
  | zero => rw [hp.node_zero]; rfl
  | succ n ih => rw [(hp.step n).1, List.length_append, ih]; rfl

/-- The node at step `n` of a legal play restricts to the node at any earlier step. -/
lemma prioritized_borel_reverse_edge_deterministic_positional_take
    {Q : Type} {k : ℕ} {G : PrioritizedBorelGame Q k} {p : ℕ → TreeGameEdge Q k}
    (hp : prioritized_borel_reverse_edge_deterministic_positional_legal G p) :
    ∀ (n m : ℕ), m ≤ n → (p n).source_node.take m = (p m).source_node := by
  intro n
  induction n with
  | zero =>
    intro m hm
    have hm0 : m = 0 := by omega
    subst hm0
    rw [hp.node_zero]
    rfl
  | succ n ih =>
    intro m hm
    rcases Nat.lt_or_ge m (n+1) with hlt | hge
    · have hm' : m ≤ n := by omega
      rw [(hp.step n).1, List.take_append]
      have hzero : m - (p n).source_node.length = 0 := by
        rw [prioritized_borel_reverse_edge_deterministic_positional_node_length hp n]; omega
      rw [hzero, List.take_zero, List.append_nil]
      exact ih m hm'
    · have hm2 : m = n + 1 := by omega
      subst hm2
      exact List.take_of_length_le (le_of_eq (prioritized_borel_reverse_edge_deterministic_positional_node_length hp (n+1)))

/-- Two legal plays that agree on node and state at step `n` agree on every state up to `n` and on every edge before `n`. -/
lemma prioritized_borel_reverse_edge_deterministic_positional_agree
    {Q : Type} {k : ℕ} {G : PrioritizedBorelGame Q k}
    (hreverse : ∀ e ∈ G.edges, ∀ e' ∈ G.edges, e.source_node = e'.source_node →
      e.dir = e'.dir → e.target_state = e'.target_state → e.source_state = e'.source_state)
    (hpriority : ∀ e ∈ G.edges, ∀ e' ∈ G.edges, e.source_node = e'.source_node →
      e.source_state = e'.source_state → e.dir = e'.dir → e.target_state = e'.target_state →
      e.prio = e'.prio)
    {p p' : ℕ → TreeGameEdge Q k}
    (hp : prioritized_borel_reverse_edge_deterministic_positional_legal G p)
    (hp' : prioritized_borel_reverse_edge_deterministic_positional_legal G p') (n : ℕ)
    (hnode : (p n).source_node = (p' n).source_node)
    (hstate : (p n).source_state = (p' n).source_state) :
    (∀ i, i ≤ n → (p i).source_state = (p' i).source_state) ∧ (∀ i, i < n → p i = p' i) := by
  have key : ∀ j i, n - i = j → i ≤ n →
      ((p i).source_state = (p' i).source_state ∧ (i < n → p i = p' i)) := by
    intro j
    induction j with
    | zero =>
      intro i hi hj
      have hin : i = n := by omega
      subst hin
      refine ⟨hstate, ?_⟩
      omega
    | succ j ih =>
      intro i hi hj
      have hin : i < n := by omega
      have hrec : n - (i+1) = j := by omega
      have hIH := (ih (i+1) hrec (by omega)).1
      have hsn : (p i).source_node = (p' i).source_node := by
        rw [← prioritized_borel_reverse_edge_deterministic_positional_take hp n i (by omega),
            ← prioritized_borel_reverse_edge_deterministic_positional_take hp' n i (by omega), hnode]
      have hdir : (p i).dir = (p' i).dir := by
        have e1 : (p i).source_node ++ [(p i).dir] = (p' i).source_node ++ [(p' i).dir] := by
          rw [← (hp.step i).1, ← (hp'.step i).1,
            ← prioritized_borel_reverse_edge_deterministic_positional_take hp n (i+1) (by omega),
            ← prioritized_borel_reverse_edge_deterministic_positional_take hp' n (i+1) (by omega), hnode]
        rw [hsn] at e1
        simpa using List.append_cancel_left e1
      have htgt : (p i).target_state = (p' i).target_state := by
        rw [← (hp.step i).2, ← (hp'.step i).2]
        exact hIH
      have hsrc : (p i).source_state = (p' i).source_state :=
        hreverse (p i) (hp.edge i) (p' i) (hp'.edge i) hsn hdir htgt
      have hprio : (p i).prio = (p' i).prio :=
        hpriority (p i) (hp.edge i) (p' i) (hp'.edge i) hsn hsrc hdir htgt
      refine ⟨hsrc, ?_⟩
      intro _
      have h1 : p i = ⟨(p i).source_node, (p i).source_state, (p i).dir, (p i).prio, (p i).target_state⟩ := rfl
      have h2 : p' i = ⟨(p' i).source_node, (p' i).source_state, (p' i).dir, (p' i).prio, (p' i).target_state⟩ := rfl
      rw [h1, h2, TreeGameEdge.mk.injEq]
      exact ⟨hsn, hsrc, hdir, hprio, htgt⟩
  exact ⟨fun i hi => (key (n - i) i rfl hi).1, fun i hi => (key (n - i) i rfl (by omega)).2 hi⟩

/-- The memory of `σ` after the first `n` moves of a play. -/
def prioritized_borel_reverse_edge_deterministic_positional_memseq
    {Q : Type} {k : ℕ} {G : PrioritizedBorelGame Q k} {pl : BorelGamePlayer} {M : Type}
    (σ : FiniteMemoryStrategy G pl M) (p : ℕ → TreeGameEdge Q k) (n : ℕ) : M :=
  Nat.rec σ.init_mem (fun j ih => σ.update ih (p j)) n

/-- Plays with the same first `n` edges induce the same memory after `n` moves. -/
lemma prioritized_borel_reverse_edge_deterministic_positional_memseq_congr
    {Q : Type} {k : ℕ} {G : PrioritizedBorelGame Q k} {pl : BorelGamePlayer} {M : Type}
    (σ : FiniteMemoryStrategy G pl M) {p p' : ℕ → TreeGameEdge Q k} :
    ∀ (n : ℕ), (∀ i, i < n → p i = p' i) →
      prioritized_borel_reverse_edge_deterministic_positional_memseq σ p n =
        prioritized_borel_reverse_edge_deterministic_positional_memseq σ p' n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro h
    show σ.update (prioritized_borel_reverse_edge_deterministic_positional_memseq σ p n) (p n) =
      σ.update (prioritized_borel_reverse_edge_deterministic_positional_memseq σ p' n) (p' n)
    rw [ih (fun i hi => h i (by omega)), h n (by omega)]

/-- Version of `memseq_congr` allowing the two step indices to differ by an equation. -/
lemma prioritized_borel_reverse_edge_deterministic_positional_memseq_index_congr
    {Q : Type} {k : ℕ} {G : PrioritizedBorelGame Q k} {pl : BorelGamePlayer} {M : Type}
    (σ : FiniteMemoryStrategy G pl M) {p p' : ℕ → TreeGameEdge Q k} {m₁ m₂ : ℕ}
    (hm : m₁ = m₂) (hp : ∀ i, i < m₁ → p i = p' i) :
    prioritized_borel_reverse_edge_deterministic_positional_memseq σ p m₁ =
      prioritized_borel_reverse_edge_deterministic_positional_memseq σ p' m₂ := by
  subst hm
  exact prioritized_borel_reverse_edge_deterministic_positional_memseq_congr σ m₁ hp

/-- The memory of `σ` at a position, reconstructed from a legal play reaching that position. -/
noncomputable def prioritized_borel_reverse_edge_deterministic_positional_posmem
    {Q : Type} {k : ℕ} {G : PrioritizedBorelGame Q k} {pl : BorelGamePlayer} {M : Type}
    (σ : FiniteMemoryStrategy G pl M) (v : List Bool) (q : Q) : M := by
  classical
  exact if h : ∃ p : ℕ → TreeGameEdge Q k,
      prioritized_borel_reverse_edge_deterministic_positional_legal G p ∧
        (p v.length).source_node = v ∧ (p v.length).source_state = q
    then prioritized_borel_reverse_edge_deterministic_positional_memseq σ (Classical.choose h) v.length
    else σ.init_mem

/-- At any position actually reached by a legal play, the reconstructed memory is the memory of `σ` along that play. -/
lemma prioritized_borel_reverse_edge_deterministic_positional_posmem_spec
    {Q : Type} {k : ℕ} {G : PrioritizedBorelGame Q k} {pl : BorelGamePlayer} {M : Type}
    (hreverse : ∀ e ∈ G.edges, ∀ e' ∈ G.edges, e.source_node = e'.source_node →
      e.dir = e'.dir → e.target_state = e'.target_state → e.source_state = e'.source_state)
    (hpriority : ∀ e ∈ G.edges, ∀ e' ∈ G.edges, e.source_node = e'.source_node →
      e.source_state = e'.source_state → e.dir = e'.dir → e.target_state = e'.target_state →
      e.prio = e'.prio)
    (σ : FiniteMemoryStrategy G pl M) {p : ℕ → TreeGameEdge Q k}
    (hp : prioritized_borel_reverse_edge_deterministic_positional_legal G p) (n : ℕ) :
    prioritized_borel_reverse_edge_deterministic_positional_memseq σ p n =
      prioritized_borel_reverse_edge_deterministic_positional_posmem σ (p n).source_node (p n).source_state := by
  classical
  have hlen : (p n).source_node.length = n :=
    prioritized_borel_reverse_edge_deterministic_positional_node_length hp n
  have hex : ∃ p' : ℕ → TreeGameEdge Q k,
      prioritized_borel_reverse_edge_deterministic_positional_legal G p' ∧
        (p' (p n).source_node.length).source_node = (p n).source_node ∧
        (p' (p n).source_node.length).source_state = (p n).source_state := by
    refine ⟨p, hp, ?_, ?_⟩ <;> rw [hlen]
  rw [prioritized_borel_reverse_edge_deterministic_positional_posmem]
  rw [dif_pos hex]
  refine prioritized_borel_reverse_edge_deterministic_positional_memseq_index_congr σ hlen.symm (fun i hi => ?_)
  obtain ⟨hleg, hnd, hst⟩ := Classical.choose_spec hex
  have hpeq : p (p n).source_node.length = p n := by
    rw [prioritized_borel_reverse_edge_deterministic_positional_node_length hp n]
  have hnd2 : (p (p n).source_node.length).source_node =
      (Classical.choose hex (p n).source_node.length).source_node := by
    rw [hpeq]; exact hnd.symm
  have hst2 : (p (p n).source_node.length).source_state =
      (Classical.choose hex (p n).source_node.length).source_state := by
    rw [hpeq]; exact hst.symm
  exact (prioritized_borel_reverse_edge_deterministic_positional_agree hreverse hpriority hp hleg
    (p n).source_node.length hnd2 hst2).2 i (by omega)

theorem prioritized_borel_reverse_edge_deterministic_positional {Q : Type} {k : ℕ} (G : PrioritizedBorelGame Q k) (pl : BorelGamePlayer) (M : Type) (σ : FiniteMemoryStrategy G pl M) (hwin : PrioritizedBorelStrategyWins G pl σ) (hreverse : ∀ e ∈ G.edges, ∀ e' ∈ G.edges, e.source_node = e'.source_node → e.dir = e'.dir → e.target_state = e'.target_state → e.source_state = e'.source_state) (hpriority : ∀ e ∈ G.edges, ∀ e' ∈ G.edges, e.source_node = e'.source_node → e.source_state = e'.source_state → e.dir = e'.dir → e.target_state = e'.target_state → e.prio = e'.prio) : ∃ τ : FiniteMemoryStrategy G pl Unit, PrioritizedBorelStrategyWins G pl τ := by
  classical
  let τ : FiniteMemoryStrategy G pl Unit :=
    { init_mem := ()
      update := fun _ _ => ()
      choice := fun _ v q =>
        if h : G.owner (v, q) = pl then
          σ.choice (prioritized_borel_reverse_edge_deterministic_positional_posmem σ v q) v q
        else Classical.choose (G.edges_outgoing v q)
      choice_edge := by
        intro m v q hq
        rw [dif_pos hq]
        exact σ.choice_edge _ v q hq }
  have hτchoice : ∀ (m : Unit) (v : List Bool) (q : Q),
      τ.choice m v q = if h : G.owner (v, q) = pl then
        σ.choice (prioritized_borel_reverse_edge_deterministic_positional_posmem σ v q) v q
        else Classical.choose (G.edges_outgoing v q) := fun _ _ _ => rfl
  have hkey : ∀ (play : ℕ → TreeGameEdge Q k),
      (∀ n, play n ∈ G.edges) → (play 0).source_node = [] →
      (∀ n, (play (n+1)).source_node = (play n).source_node ++ [(play n).dir] ∧
        (play (n+1)).source_state = (play n).target_state) →
      (∃ (mτ : ℕ → Unit), mτ 0 = τ.init_mem ∧
        (∀ n, mτ (n+1) = τ.update (mτ n) (play n)) ∧
        ∀ n, G.owner ((play n).source_node, (play n).source_state) = pl →
          play n = τ.choice (mτ n) (play n).source_node (play n).source_state) →
      ∃ (mem : ℕ → M), mem 0 = σ.init_mem ∧
        (∀ n, mem (n+1) = σ.update (mem n) (play n)) ∧
        ∀ n, G.owner ((play n).source_node, (play n).source_state) = pl →
          play n = σ.choice (mem n) (play n).source_node (play n).source_state := by
    intro play hedge hinit hsucc hconsist
    obtain ⟨mτ, -, -, hmchoice⟩ := hconsist
    have hpl : prioritized_borel_reverse_edge_deterministic_positional_legal G play :=
      ⟨hedge, hinit, hsucc⟩
    refine ⟨fun n => prioritized_borel_reverse_edge_deterministic_positional_memseq σ play n,
      rfl, fun n => rfl, ?_⟩
    intro n hn
    have h1 : play n = τ.choice (mτ n) (play n).source_node (play n).source_state := hmchoice n hn
    have hτc : τ.choice (mτ n) (play n).source_node (play n).source_state =
        σ.choice (prioritized_borel_reverse_edge_deterministic_positional_memseq σ play n)
          (play n).source_node (play n).source_state := by
      rw [hτchoice (mτ n) (play n).source_node (play n).source_state, dif_pos hn,
        ← prioritized_borel_reverse_edge_deterministic_positional_posmem_spec hreverse hpriority σ hpl n]
    exact h1.trans hτc
  refine ⟨τ, ?_⟩
  intro play hedge hinit hsucc hconsist
  have hwit := hkey play hedge hinit.1 hsucc hconsist
  cases pl with
  | Eve => exact hwin play hedge hinit hsucc hwit
  | Adam => exact hwin play hedge hinit hsucc hwit
