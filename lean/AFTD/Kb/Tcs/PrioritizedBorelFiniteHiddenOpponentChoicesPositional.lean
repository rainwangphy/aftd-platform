import AFTD.Prelude
import AFTD.Kb.Tcs.PrioritizedBorelGame
import AFTD.Kb.Tcs.FiniteMemoryStrategy
import AFTD.Kb.Tcs.PrioritizedBorelStrategyWins
import AFTD.Kb.Tcs.TreeGameEdge
import AFTD.Kb.Tcs.BorelGamePlayer
import AFTD.Kb.Tcs.PrioritizedBorelStrategyHistory
import AFTD.Kb.Tcs.PrioritizedBorelEventualHiddenShadow
import AFTD.Kb.Tcs.PrioritizedBorelPayoffTailCongr
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# prioritized_borel_finite_hidden_opponent_choices_positional

Topic: automata   Node: ea99bcf7e6a7

Provenance: original. Related work: Eventual hidden-choice strategy compression related to arXiv:2611.10136, Conjecture 19.

Fix a winning strategy in a prioritized tree game, with an arbitrary state type. Suppose that on every legal play, all but finitely many opponent moves are uniquely determined by their public branch direction and current position. Then the same player has a memoryless winning strategy. The opponent may choose different branch directions infinitely often; only same-direction hidden choices must eventually cease.
-/

abbrev op1385Sig (Q : Type) (k : ℕ) := Bool × Q × Fin k

def op1385EdgeSig {Q : Type} {k : ℕ} (e : TreeGameEdge Q k) : op1385Sig Q k :=
  (e.dir, e.target_state, e.prio)

def op1385MakeEdge {Q : Type} {k : ℕ} (v : List Bool) (q : Q)
    (a : op1385Sig Q k) : TreeGameEdge Q k where
  source_node := v
  source_state := q
  dir := a.1
  prio := a.2.2
  target_state := a.2.1

def op1385EvalStep {Q M : Type} {k : ℕ} (G : PrioritizedBorelGame Q k)
    (pl : BorelGamePlayer) (σ : FiniteMemoryStrategy G pl M)
    (st : M × List Bool × Q) (a : op1385Sig Q k) : M × List Bool × Q :=
  (σ.update st.1 (op1385MakeEdge st.2.1 st.2.2 a), st.2.1 ++ [a.1], a.2.1)

def op1385Eval {Q M : Type} {k : ℕ} (G : PrioritizedBorelGame Q k)
    (pl : BorelGamePlayer) (σ : FiniteMemoryStrategy G pl M)
    (h : List (op1385Sig Q k)) : M × List Bool × Q :=
  h.foldl (op1385EvalStep G pl σ) (σ.init_mem, [], G.init_state)

lemma op1385_eval_snoc {Q M : Type} {k : ℕ} (G : PrioritizedBorelGame Q k)
    (pl : BorelGamePlayer) (σ : FiniteMemoryStrategy G pl M)
    (h : List (op1385Sig Q k)) (a : op1385Sig Q k) :
    op1385Eval G pl σ (h ++ [a]) = op1385EvalStep G pl σ (op1385Eval G pl σ h) a := by
  simp [op1385Eval, List.foldl_append]

lemma op1385_make_sig {Q : Type} {k : ℕ} (e : TreeGameEdge Q k) :
    op1385MakeEdge e.source_node e.source_state (op1385EdgeSig e) = e := by
  cases e
  rfl

theorem op1385_eval_history {Q M : Type} {k : ℕ} (G : PrioritizedBorelGame Q k)
    (pl : BorelGamePlayer) (σ : FiniteMemoryStrategy G pl M)
    (h : List (op1385Sig Q k)) (m : M) (v : List Bool) (q : Q)
    (hh : PrioritizedBorelStrategyHistory G pl σ h m v q) :
    op1385Eval G pl σ h = (m, v, q) := by
  induction hh with
  | root => rfl
  | @step h m v q e hh he hnode hstate hchoice ih =>
    rw [op1385_eval_snoc, ih]
    simp only [op1385EvalStep, op1385EdgeSig]
    have hm : op1385MakeEdge e.source_node e.source_state
        (e.dir, e.target_state, e.prio) = e := op1385_make_sig e
    rw [← hnode, ← hstate, hm]

theorem op1385_history_prefix {Q M : Type} {k : ℕ} (G : PrioritizedBorelGame Q k)
    (pl : BorelGamePlayer) (σ : FiniteMemoryStrategy G pl M)
    (h : List (op1385Sig Q k)) (m : M) (v : List Bool) (q : Q)
    (hh : PrioritizedBorelStrategyHistory G pl σ h m v q)
    (p : List (op1385Sig Q k)) (hp : p <+: h) :
    ∃ m' v' q', PrioritizedBorelStrategyHistory G pl σ p m' v' q' := by
  induction hh generalizing p with
  | root =>
    have hp0 : p = [] := List.eq_nil_of_prefix_nil hp
    subst p
    exact ⟨σ.init_mem, [], G.init_state, PrioritizedBorelStrategyHistory.root⟩
  | @step h m v q e hh he hv hq hc ih =>
    rcases List.prefix_concat_iff.mp hp with hfull | hshort
    · subst p
      exact ⟨σ.update m e, v ++ [e.dir], e.target_state,
        PrioritizedBorelStrategyHistory.step e hh he hv hq hc⟩
    · exact ih p hshort

theorem op1385_history_snoc_inv {Q M : Type} {k : ℕ} (G : PrioritizedBorelGame Q k)
    (pl : BorelGamePlayer) (σ : FiniteMemoryStrategy G pl M)
    (xs : List (op1385Sig Q k)) (m : M) (v : List Bool) (q : Q)
    (hh : PrioritizedBorelStrategyHistory G pl σ xs m v q)
    (h : List (op1385Sig Q k)) (a : op1385Sig Q k) (heq : xs = h ++ [a]) :
    ∃ (m₀ : M) (v₀ : List Bool) (q₀ : Q) (e : TreeGameEdge Q k),
      PrioritizedBorelStrategyHistory G pl σ h m₀ v₀ q₀ ∧
      e ∈ G.edges ∧ e.source_node = v₀ ∧ e.source_state = q₀ ∧
      (G.owner (v₀, q₀) = pl → e = σ.choice m₀ v₀ q₀) ∧
      op1385EdgeSig e = a ∧ m = σ.update m₀ e ∧ v = v₀ ++ [e.dir] ∧ q = e.target_state := by
  induction hh generalizing h a with
  | root => simp at heq
  | @step h₀ m₀ v₀ q₀ e hh he hv hq hc ih =>
    have hpre : h₀ = h := List.append_inj_left' heq (by simp)
    have ha : op1385EdgeSig e = a := by
      simpa [op1385EdgeSig] using congrArg List.getLast? heq
    subst h
    exact ⟨m₀, v₀, q₀, e, hh, he, hv, hq, hc, ha, rfl, rfl, rfl⟩

theorem op1385_all_shadow_prefixes {Q M : Type} {k : ℕ}
    (G : PrioritizedBorelGame Q k) (pl : BorelGamePlayer) (σ : FiniteMemoryStrategy G pl M)
    (histories : ℕ → List (op1385Sig Q k)) (f : ℕ → op1385Sig Q k) (K : ℕ)
    (hrep : ∀ n, ∃ m v q, PrioritizedBorelStrategyHistory G pl σ (histories n) m v q)
    (hprefix : ∀ n ≥ K, List.ofFn (fun i : Fin n => f i) = histories n) :
    ∀ n, ∃ m v q, PrioritizedBorelStrategyHistory G pl σ
      (List.ofFn (fun i : Fin n => f i)) m v q := by
  intro n
  by_cases hn : K ≤ n
  · rw [hprefix n hn]
    exact hrep n
  · obtain ⟨m, v, q, hh⟩ := hrep K
    have hp := op1385_ofFn_prefix f (show n ≤ K by omega)
    rw [hprefix K (le_refl K)] at hp
    exact op1385_history_prefix G pl σ (histories K) m v q hh _ hp

def op1385FnPrefix {A : Type} (f : ℕ → A) (n : ℕ) : List A :=
  List.ofFn (fun i : Fin n => f i)

lemma op1385_fn_prefix_succ {A : Type} (f : ℕ → A) (n : ℕ) :
    op1385FnPrefix f (n+1) = op1385FnPrefix f n ++ [f n] := by
  simpa [op1385FnPrefix, List.concat_eq_append] using
    (List.ofFn_succ' (fun i : Fin (n+1) => f i))

def op1385ShadowEdge {Q M : Type} {k : ℕ} (G : PrioritizedBorelGame Q k)
    (pl : BorelGamePlayer) (σ : FiniteMemoryStrategy G pl M)
    (f : ℕ → op1385Sig Q k) (n : ℕ) : TreeGameEdge Q k :=
  let st := op1385Eval G pl σ (op1385FnPrefix f n)
  op1385MakeEdge st.2.1 st.2.2 (f n)

theorem op1385_shadow_play_of_histories {Q M : Type} {k : ℕ}
    (G : PrioritizedBorelGame Q k) (pl : BorelGamePlayer) (σ : FiniteMemoryStrategy G pl M)
    (f : ℕ → op1385Sig Q k)
    (hh : ∀ n, ∃ m v q, PrioritizedBorelStrategyHistory G pl σ (op1385FnPrefix f n) m v q) :
    let π := op1385ShadowEdge G pl σ f
    (∀ n, π n ∈ G.edges) ∧
    ((π 0).source_node = [] ∧ (π 0).source_state = G.init_state) ∧
    (∀ n, (π (n+1)).source_node = (π n).source_node ++ [(π n).dir] ∧
      (π (n+1)).source_state = (π n).target_state) ∧
    (∃ mem : ℕ → M, mem 0 = σ.init_mem ∧ (∀ n, mem (n+1) = σ.update (mem n) (π n)) ∧
      (∀ n, G.owner ((π n).source_node, (π n).source_state) = pl →
        π n = σ.choice (mem n) (π n).source_node (π n).source_state)) := by
  classical
  let π := op1385ShadowEdge G pl σ f
  let mem : ℕ → M := fun n => (op1385Eval G pl σ (op1385FnPrefix f n)).1
  have hstep (n : ℕ) : π n ∈ G.edges ∧
      (G.owner ((π n).source_node, (π n).source_state) = pl →
        π n = σ.choice (mem n) (π n).source_node (π n).source_state) := by
    obtain ⟨m, v, q, hhist⟩ := hh (n+1)
    obtain ⟨m₀, v₀, q₀, e, hhist₀, he, hv, hq, hc, ha, _, _, _⟩ :=
      op1385_history_snoc_inv G pl σ (op1385FnPrefix f (n+1)) m v q hhist
        (op1385FnPrefix f n) (f n) (op1385_fn_prefix_succ f n)
    have heval := op1385_eval_history G pl σ _ m₀ v₀ q₀ hhist₀
    have heq : π n = e := by
      dsimp [π, op1385ShadowEdge]
      rw [heval, ← ha, ← hv, ← hq, op1385_make_sig]
    refine ⟨?_, ?_⟩
    · rw [heq]
      exact he
    intro howner
    rw [heq] at howner ⊢
    have hc' := hc (by simpa [hv, hq] using howner)
    simpa [mem, heval, hv, hq] using hc'
  refine ⟨fun n => (hstep n).1, ?_, ?_, ?_⟩
  · simp [π, op1385ShadowEdge, op1385FnPrefix, op1385Eval, op1385MakeEdge]
  · intro n
    change (op1385Eval G pl σ (op1385FnPrefix f (n+1))).2.1 =
        (op1385Eval G pl σ (op1385FnPrefix f n)).2.1 ++ [(f n).1] ∧
      (op1385Eval G pl σ (op1385FnPrefix f (n+1))).2.2 = (f n).2.1
    rw [op1385_fn_prefix_succ, op1385_eval_snoc]
    constructor <;> rfl
  · refine ⟨mem, ?_, ?_, fun n => (hstep n).2⟩
    · simp [mem, op1385FnPrefix, op1385Eval]
    · intro n
      change (op1385Eval G pl σ (op1385FnPrefix f (n+1))).1 =
        σ.update (op1385Eval G pl σ (op1385FnPrefix f n)).1
          (op1385ShadowEdge G pl σ f n)
      rw [op1385_fn_prefix_succ, op1385_eval_snoc]
      rfl

theorem op1385_eval_node {Q M : Type} {k : ℕ} (G : PrioritizedBorelGame Q k)
    (pl : BorelGamePlayer) (σ : FiniteMemoryStrategy G pl M)
    (h : List (op1385Sig Q k)) :
    (op1385Eval G pl σ h).2.1 = h.map Prod.fst := by
  induction h using List.reverseRecOn with
  | nil => rfl
  | @append_singleton a h ih =>
    rw [op1385_eval_snoc]
    simp [op1385EvalStep, List.map_append, ih]

noncomputable def op1385Own {Q M : Type} {k : ℕ} (G : PrioritizedBorelGame Q k)
    (pl : BorelGamePlayer) (σ : FiniteMemoryStrategy G pl M)
    (h : List (op1385Sig Q k)) : Bool := by
  classical
  let st := op1385Eval G pl σ h
  exact decide (G.owner (st.2.1, st.2.2) = pl)

noncomputable def op1385Hidden {Q M : Type} {k : ℕ} (G : PrioritizedBorelGame Q k)
    (pl : BorelGamePlayer) (σ : FiniteMemoryStrategy G pl M)
    (h : List (op1385Sig Q k)) (b : Bool) : Bool := by
  classical
  let st := op1385Eval G pl σ h
  exact decide (∃ e ∈ G.edges, ∃ e' ∈ G.edges,
    e.source_node = st.2.1 ∧ e.source_state = st.2.2 ∧ e.dir = b ∧
    e'.source_node = st.2.1 ∧ e'.source_state = st.2.2 ∧ e'.dir = b ∧ e ≠ e')

def op1385Policy {Q M : Type} {k : ℕ} (G : PrioritizedBorelGame Q k)
    (pl : BorelGamePlayer) (σ : FiniteMemoryStrategy G pl M)
    (h : List (op1385Sig Q k)) : op1385Sig Q k :=
  let st := op1385Eval G pl σ h
  op1385EdgeSig (σ.choice st.1 st.2.1 st.2.2)

noncomputable def op1385Forced {Q M : Type} {k : ℕ} (G : PrioritizedBorelGame Q k)
    (pl : BorelGamePlayer) (σ : FiniteMemoryStrategy G pl M)
    (h : List (op1385Sig Q k)) (b : Bool) : op1385Sig Q k := by
  classical
  let st := op1385Eval G pl σ h
  exact if hex : ∃ e ∈ G.edges,
      e.source_node = st.2.1 ∧ e.source_state = st.2.2 ∧ e.dir = b
    then op1385EdgeSig (Classical.choose hex)
    else op1385EdgeSig (σ.choice st.1 st.2.1 st.2.2)

lemma op1385_hidden_false_unique {Q M : Type} {k : ℕ} (G : PrioritizedBorelGame Q k)
    (pl : BorelGamePlayer) (σ : FiniteMemoryStrategy G pl M)
    (h : List (op1385Sig Q k)) (b : Bool)
    (e e' : TreeGameEdge Q k) (he : e ∈ G.edges) (he' : e' ∈ G.edges)
    (hv : e.source_node = (op1385Eval G pl σ h).2.1)
    (hq : e.source_state = (op1385Eval G pl σ h).2.2) (hd : e.dir = b)
    (hv' : e'.source_node = (op1385Eval G pl σ h).2.1)
    (hq' : e'.source_state = (op1385Eval G pl σ h).2.2) (hd' : e'.dir = b)
    (hhidden : op1385Hidden G pl σ h b = false) : e = e' := by
  classical
  have hn : ¬ ∃ a ∈ G.edges, ∃ a' ∈ G.edges,
      a.source_node = (op1385Eval G pl σ h).2.1 ∧
      a.source_state = (op1385Eval G pl σ h).2.2 ∧ a.dir = b ∧
      a'.source_node = (op1385Eval G pl σ h).2.1 ∧
      a'.source_state = (op1385Eval G pl σ h).2.2 ∧ a'.dir = b ∧ a ≠ a' := by
    simpa [op1385Hidden] using hhidden
  by_contra hne
  exact hn ⟨e, he, e', he', hv, hq, hd, hv', hq', hd', hne⟩

lemma op1385_forced_eq {Q M : Type} {k : ℕ} (G : PrioritizedBorelGame Q k)
    (pl : BorelGamePlayer) (σ : FiniteMemoryStrategy G pl M)
    (h : List (op1385Sig Q k)) (e : TreeGameEdge Q k) (he : e ∈ G.edges)
    (hv : e.source_node = (op1385Eval G pl σ h).2.1)
    (hq : e.source_state = (op1385Eval G pl σ h).2.2)
    (hhidden : op1385Hidden G pl σ h e.dir = false) :
    op1385Forced G pl σ h e.dir = op1385EdgeSig e := by
  classical
  have hex : ∃ a ∈ G.edges,
      a.source_node = (op1385Eval G pl σ h).2.1 ∧
      a.source_state = (op1385Eval G pl σ h).2.2 ∧ a.dir = e.dir :=
    ⟨e, he, hv, hq, rfl⟩
  have hs := Classical.choose_spec hex
  have hsame : Classical.choose hex = e :=
    op1385_hidden_false_unique G pl σ h e.dir (Classical.choose hex) e
      hs.1 he hs.2.1 hs.2.2.1 hs.2.2.2 hv hq rfl hhidden
  unfold op1385Forced
  simp only [dif_pos hex, hsame]

theorem op1385_history_hidden_compatible {Q M : Type} {k : ℕ}
    (G : PrioritizedBorelGame Q k) (pl : BorelGamePlayer) (σ : FiniteMemoryStrategy G pl M)
    (h : List (op1385Sig Q k)) (m : M) (v : List Bool) (q : Q)
    (hh : PrioritizedBorelStrategyHistory G pl σ h m v q) :
    op1385HiddenCompatible Prod.fst (op1385Own G pl σ) (op1385Hidden G pl σ)
      (op1385Policy G pl σ) (op1385Forced G pl σ) [] h := by
  classical
  induction hh with
  | root => trivial
  | @step h m v q e hh he hnode hstate hchoice ih =>
    apply (op1385_hidden_compatible_snoc Prod.fst (op1385Own G pl σ)
      (op1385Hidden G pl σ) (op1385Policy G pl σ) (op1385Forced G pl σ)
      [] h (op1385EdgeSig e)).2
    refine ⟨ih, ?_⟩
    simp only [List.nil_append]
    have heval := op1385_eval_history G pl σ h m v q hh
    have hnode' : e.source_node = (op1385Eval G pl σ h).2.1 := by simpa [heval] using hnode
    have hstate' : e.source_state = (op1385Eval G pl σ h).2.2 := by simpa [heval] using hstate
    by_cases howner : G.owner (v, q) = pl
    · have ho : op1385Own G pl σ h = true := by simp [op1385Own, heval, howner]
      have hs : op1385EdgeSig e = op1385Policy G pl σ h := by
        simp only [op1385Policy, heval]
        rw [hchoice howner]
      simp [op1385HiddenStep, ho, hs]
    · have ho : op1385Own G pl σ h = false := by simp [op1385Own, heval, howner]
      cases hhidden : op1385Hidden G pl σ h e.dir with
      | true => simp [op1385HiddenStep, ho, op1385EdgeSig, hhidden]
      | false =>
        have hf := op1385_forced_eq G pl σ h e he hnode' hstate' hhidden
        simpa [op1385HiddenStep, ho, op1385EdgeSig, hhidden] using hf.symm

def op1385ReachableRecords {Q M : Type} {k : ℕ} (G : PrioritizedBorelGame Q k)
    (pl : BorelGamePlayer) (σ : FiniteMemoryStrategy G pl M)
    (v : List Bool) (q : Q) : Set (List (op1385Sig Q k)) :=
  {r | ∃ h m, PrioritizedBorelStrategyHistory G pl σ h m v q ∧
    op1385HiddenRecord Prod.fst (op1385Own G pl σ) (op1385Hidden G pl σ) [] h = r}

noncomputable def op1385BestRecord {Q M : Type} {k : ℕ}
    [LinearOrder (List (op1385Sig Q k))] [WellFoundedLT (List (op1385Sig Q k))]
    (G : PrioritizedBorelGame Q k) (pl : BorelGamePlayer) (σ : FiniteMemoryStrategy G pl M)
    (v : List Bool) (q : Q) : List (op1385Sig Q k) := by
  classical
  let S := op1385ReachableRecords G pl σ v q
  exact if hs : S.Nonempty then Classical.choose (wellFounded_lt.has_min S hs) else []

lemma op1385_best_record_spec {Q M : Type} {k : ℕ}
    [LinearOrder (List (op1385Sig Q k))] [WellFoundedLT (List (op1385Sig Q k))]
    (G : PrioritizedBorelGame Q k) (pl : BorelGamePlayer) (σ : FiniteMemoryStrategy G pl M)
    (v : List Bool) (q : Q) (hs : (op1385ReachableRecords G pl σ v q).Nonempty) :
    op1385BestRecord G pl σ v q ∈ op1385ReachableRecords G pl σ v q ∧
      ∀ r ∈ op1385ReachableRecords G pl σ v q, op1385BestRecord G pl σ v q ≤ r := by
  classical
  have hmin := Classical.choose_spec (wellFounded_lt.has_min (op1385ReachableRecords G pl σ v q) hs)
  have hbest : op1385BestRecord G pl σ v q =
      Classical.choose (wellFounded_lt.has_min (op1385ReachableRecords G pl σ v q) hs) := by
    simp [op1385BestRecord, hs]
  rw [hbest]
  refine ⟨hmin.1, ?_⟩
  intro r hr
  exact le_of_not_gt (hmin.2 r hr)

noncomputable def op1385Representative {Q M : Type} {k : ℕ}
    [LinearOrder (List (op1385Sig Q k))] [WellFoundedLT (List (op1385Sig Q k))]
    (G : PrioritizedBorelGame Q k) (pl : BorelGamePlayer) (σ : FiniteMemoryStrategy G pl M)
    (v : List Bool) (q : Q) : List (op1385Sig Q k) := by
  classical
  let S := op1385ReachableRecords G pl σ v q
  exact if hs : S.Nonempty then
    Classical.choose ((op1385_best_record_spec G pl σ v q hs).1) else []

lemma op1385_representative_spec {Q M : Type} {k : ℕ}
    [LinearOrder (List (op1385Sig Q k))] [WellFoundedLT (List (op1385Sig Q k))]
    (G : PrioritizedBorelGame Q k) (pl : BorelGamePlayer) (σ : FiniteMemoryStrategy G pl M)
    (v : List Bool) (q : Q) (hs : (op1385ReachableRecords G pl σ v q).Nonempty) :
    ∃ m, PrioritizedBorelStrategyHistory G pl σ (op1385Representative G pl σ v q) m v q ∧
      op1385HiddenRecord Prod.fst (op1385Own G pl σ) (op1385Hidden G pl σ) []
        (op1385Representative G pl σ v q) = op1385BestRecord G pl σ v q := by
  classical
  have hmem := (op1385_best_record_spec G pl σ v q hs).1
  have hrep : op1385Representative G pl σ v q = Classical.choose hmem := by
    simp [op1385Representative, hs]
  rw [hrep]
  exact Classical.choose_spec hmem

noncomputable def op1385Fallback {Q : Type} {k : ℕ} (G : PrioritizedBorelGame Q k)
    (v : List Bool) (q : Q) : TreeGameEdge Q k :=
  Classical.choose (G.edges_outgoing v q)

lemma op1385_fallback_spec {Q : Type} {k : ℕ} (G : PrioritizedBorelGame Q k)
    (v : List Bool) (q : Q) : op1385Fallback G v q ∈ G.edges ∧
    (op1385Fallback G v q).source_node = v ∧ (op1385Fallback G v q).source_state = q :=
  Classical.choose_spec (G.edges_outgoing v q)

noncomputable def op1385Positional {Q M : Type} {k : ℕ}
    [LinearOrder (List (op1385Sig Q k))] [WellFoundedLT (List (op1385Sig Q k))]
    (G : PrioritizedBorelGame Q k) (pl : BorelGamePlayer) (σ : FiniteMemoryStrategy G pl M) :
    FiniteMemoryStrategy G pl Unit where
  init_mem := ()
  update := fun _ _ => ()
  choice := fun _ v q => by
    classical
    exact if (op1385ReachableRecords G pl σ v q).Nonempty then
      σ.choice (op1385Eval G pl σ (op1385Representative G pl σ v q)).1 v q
    else op1385Fallback G v q
  choice_edge := by
    classical
    intro _ v q howner
    split
    · exact σ.choice_edge _ v q howner
    · exact op1385_fallback_spec G v q

lemma op1385_representative_extend {Q M : Type} {k : ℕ}
    [LinearOrder (List (op1385Sig Q k))] [WellFoundedLT (List (op1385Sig Q k))]
    (G : PrioritizedBorelGame Q k) (pl : BorelGamePlayer) (σ : FiniteMemoryStrategy G pl M)
    (v : List Bool) (q : Q) (hs : (op1385ReachableRecords G pl σ v q).Nonempty)
    (e : TreeGameEdge Q k) (he : e ∈ G.edges) (hv : e.source_node = v) (hq : e.source_state = q)
    (hchosen : G.owner (v, q) = pl →
      e = σ.choice (op1385Eval G pl σ (op1385Representative G pl σ v q)).1 v q) :
    ∃ m, PrioritizedBorelStrategyHistory G pl σ
      (op1385Representative G pl σ v q ++ [op1385EdgeSig e]) m (v ++ [e.dir]) e.target_state := by
  obtain ⟨m, hh, _⟩ := op1385_representative_spec G pl σ v q hs
  have heval := op1385_eval_history G pl σ _ m v q hh
  refine ⟨σ.update m e, PrioritizedBorelStrategyHistory.step e hh he hv hq ?_⟩
  intro howner
  simpa [heval] using hchosen howner

lemma op1385_next_record_bound {Q M : Type} {k : ℕ}
    [LinearOrder (List (op1385Sig Q k))] [WellFoundedLT (List (op1385Sig Q k))]
    (G : PrioritizedBorelGame Q k) (pl : BorelGamePlayer) (σ : FiniteMemoryStrategy G pl M)
    (v : List Bool) (q : Q) (hs : (op1385ReachableRecords G pl σ v q).Nonempty)
    (e : TreeGameEdge Q k) (he : e ∈ G.edges) (hv : e.source_node = v) (hq : e.source_state = q)
    (hchosen : G.owner (v, q) = pl →
      e = σ.choice (op1385Eval G pl σ (op1385Representative G pl σ v q)).1 v q) :
    (op1385ReachableRecords G pl σ (v ++ [e.dir]) e.target_state).Nonempty ∧
    op1385BestRecord G pl σ (v ++ [e.dir]) e.target_state ≤
      op1385HiddenRecord Prod.fst (op1385Own G pl σ) (op1385Hidden G pl σ) []
        (op1385Representative G pl σ v q ++ [op1385EdgeSig e]) := by
  obtain ⟨m, hh⟩ := op1385_representative_extend G pl σ v q hs e he hv hq hchosen
  let r := op1385HiddenRecord Prod.fst (op1385Own G pl σ) (op1385Hidden G pl σ) []
    (op1385Representative G pl σ v q ++ [op1385EdgeSig e])
  have hr : r ∈ op1385ReachableRecords G pl σ (v ++ [e.dir]) e.target_state := by
    exact ⟨_, m, hh, rfl⟩
  have hne : (op1385ReachableRecords G pl σ (v ++ [e.dir]) e.target_state).Nonempty := ⟨r, hr⟩
  exact ⟨hne, (op1385_best_record_spec G pl σ (v ++ [e.dir]) e.target_state hne).2 r hr⟩

theorem op1385_positional_reachable {Q M : Type} {k : ℕ}
    [LinearOrder (List (op1385Sig Q k))] [WellFoundedLT (List (op1385Sig Q k))]
    (G : PrioritizedBorelGame Q k) (pl : BorelGamePlayer) (σ : FiniteMemoryStrategy G pl M)
    (π : ℕ → TreeGameEdge Q k) (hlegal : ∀ n, π n ∈ G.edges)
    (hinit : (π 0).source_node = [] ∧ (π 0).source_state = G.init_state)
    (hnext : ∀ n, (π (n+1)).source_node = (π n).source_node ++ [(π n).dir] ∧
      (π (n+1)).source_state = (π n).target_state)
    (hfollow : ∀ n, G.owner ((π n).source_node, (π n).source_state) = pl →
      π n = (op1385Positional G pl σ).choice () (π n).source_node (π n).source_state) :
    ∀ n, (op1385ReachableRecords G pl σ (π n).source_node (π n).source_state).Nonempty := by
  classical
  intro n
  induction n with
  | zero =>
    rw [hinit.1, hinit.2]
    refine ⟨[], [], σ.init_mem, PrioritizedBorelStrategyHistory.root, ?_⟩
    rfl
  | succ n ih =>
    have hc : G.owner ((π n).source_node, (π n).source_state) = pl →
        π n = σ.choice (op1385Eval G pl σ
          (op1385Representative G pl σ (π n).source_node (π n).source_state)).1
          (π n).source_node (π n).source_state := by
      intro howner
      simpa [op1385Positional, ih] using hfollow n howner
    have hbound := op1385_next_record_bound G pl σ (π n).source_node (π n).source_state
      ih (π n) (hlegal n) rfl rfl hc
    rw [(hnext n).1, (hnext n).2]
    exact hbound.1

lemma op1385_extension_record_unchanged {Q M : Type} {k : ℕ}
    [LinearOrder (List (op1385Sig Q k))] [WellFoundedLT (List (op1385Sig Q k))]
    (G : PrioritizedBorelGame Q k) (pl : BorelGamePlayer) (σ : FiniteMemoryStrategy G pl M)
    (v : List Bool) (q : Q) (hs : (op1385ReachableRecords G pl σ v q).Nonempty)
    (e : TreeGameEdge Q k) (he : e ∈ G.edges) (hv : e.source_node = v) (hq : e.source_state = q)
    (hnonhidden : G.owner (v, q) = pl ∨ ∀ e' ∈ G.edges,
      e'.source_node = v → e'.source_state = q → e'.dir = e.dir → e' = e) :
    op1385HiddenRecord Prod.fst (op1385Own G pl σ) (op1385Hidden G pl σ) []
      (op1385Representative G pl σ v q ++ [op1385EdgeSig e]) =
    op1385BestRecord G pl σ v q := by
  classical
  obtain ⟨m, hh, hrec⟩ := op1385_representative_spec G pl σ v q hs
  have heval := op1385_eval_history G pl σ _ m v q hh
  have hstore : (!op1385Own G pl σ (op1385Representative G pl σ v q) &&
      op1385Hidden G pl σ (op1385Representative G pl σ v q) e.dir) = false := by
    rcases hnonhidden with howner | hunique
    · simp [op1385Own, heval, howner]
    · have hn : ¬ ∃ a ∈ G.edges, ∃ a' ∈ G.edges,
          a.source_node = v ∧ a.source_state = q ∧ a.dir = e.dir ∧
          a'.source_node = v ∧ a'.source_state = q ∧ a'.dir = e.dir ∧ a ≠ a' := by
        rintro ⟨a, ha, a', ha', hav, haq, had, hav', haq', had', hne⟩
        exact hne ((hunique a ha hav haq had).trans (hunique a' ha' hav' haq' had').symm)
      have hhfalse : op1385Hidden G pl σ (op1385Representative G pl σ v q) e.dir = false := by
        simpa [op1385Hidden, heval] using hn
      simp [hhfalse]
  rw [op1385_hidden_record_snoc]
  simpa [op1385EdgeSig, hstore] using hrec

theorem op1385_positional_representatives_stabilize {Q M : Type} {k : ℕ}
    [LinearOrder (List (op1385Sig Q k))] [WellFoundedLT (List (op1385Sig Q k))]
    (G : PrioritizedBorelGame Q k) (pl : BorelGamePlayer) (σ : FiniteMemoryStrategy G pl M)
    (π : ℕ → TreeGameEdge Q k) (hlegal : ∀ n, π n ∈ G.edges)
    (hinit : (π 0).source_node = [] ∧ (π 0).source_state = G.init_state)
    (hnext : ∀ n, (π (n+1)).source_node = (π n).source_node ++ [(π n).dir] ∧
      (π (n+1)).source_state = (π n).target_state)
    (hfollow : ∀ n, G.owner ((π n).source_node, (π n).source_state) = pl →
      π n = (op1385Positional G pl σ).choice () (π n).source_node (π n).source_state)
    (N : ℕ) (hnonhidden : ∀ n ≥ N, G.owner ((π n).source_node, (π n).source_state) = pl ∨
      ∀ e ∈ G.edges, e.source_node = (π n).source_node →
        e.source_state = (π n).source_state → e.dir = (π n).dir → e = π n) :
    ∃ K ≥ N, ∀ n ≥ K,
      op1385Representative G pl σ (π (n+1)).source_node (π (n+1)).source_state =
      op1385Representative G pl σ (π n).source_node (π n).source_state ++ [op1385EdgeSig (π n)] := by
  classical
  let histories : ℕ → List (op1385Sig Q k) := fun n =>
    op1385Representative G pl σ (π n).source_node (π n).source_state
  let actual : ℕ → op1385Sig Q k := fun n => op1385EdgeSig (π n)
  have hreach := op1385_positional_reachable G pl σ π hlegal hinit hnext hfollow
  have hrep (n : ℕ) : ∃ m, PrioritizedBorelStrategyHistory G pl σ (histories n) m
      (π n).source_node (π n).source_state ∧
      op1385HiddenRecord Prod.fst (op1385Own G pl σ) (op1385Hidden G pl σ) [] (histories n) =
        op1385BestRecord G pl σ (π n).source_node (π n).source_state :=
    op1385_representative_spec G pl σ (π n).source_node (π n).source_state (hreach n)
  have hcompat (n : ℕ) : op1385HiddenCompatible Prod.fst (op1385Own G pl σ)
      (op1385Hidden G pl σ) (op1385Policy G pl σ) (op1385Forced G pl σ) [] (histories n) := by
    obtain ⟨m, hh, _⟩ := hrep n
    exact op1385_history_hidden_compatible G pl σ _ m _ _ hh
  have hnode (n : ℕ) : (histories n).map Prod.fst = (π n).source_node := by
    obtain ⟨m, hh, _⟩ := hrep n
    have heval := op1385_eval_history G pl σ (histories n) m _ _ hh
    simpa [heval] using (op1385_eval_node G pl σ (histories n)).symm
  have hdir (n : ℕ) : (histories (n+1)).map Prod.fst =
      (histories n).map Prod.fst ++ [Prod.fst (actual n)] := by
    rw [hnode (n+1), hnode n, (hnext n).1]
    rfl
  have hchosen (n : ℕ) : G.owner ((π n).source_node, (π n).source_state) = pl →
      π n = σ.choice (op1385Eval G pl σ (histories n)).1
        (π n).source_node (π n).source_state := by
    intro howner
    simpa [histories, op1385Positional, hreach n] using hfollow n howner
  have hext (n : ℕ) : op1385HiddenCompatible Prod.fst (op1385Own G pl σ)
      (op1385Hidden G pl σ) (op1385Policy G pl σ) (op1385Forced G pl σ) []
      (histories n ++ [actual n]) := by
    obtain ⟨m, hh⟩ := op1385_representative_extend G pl σ (π n).source_node (π n).source_state
      (hreach n) (π n) (hlegal n) rfl rfl (hchosen n)
    exact op1385_history_hidden_compatible G pl σ _ m _ _ hh
  have hrecord (n : ℕ) (hn : N ≤ n) :
      op1385HiddenRecord Prod.fst (op1385Own G pl σ) (op1385Hidden G pl σ) []
        (histories n ++ [actual n]) =
      op1385HiddenRecord Prod.fst (op1385Own G pl σ) (op1385Hidden G pl σ) [] (histories n) := by
    have heq := op1385_extension_record_unchanged G pl σ (π n).source_node (π n).source_state
      (hreach n) (π n) (hlegal n) rfl rfl (hnonhidden n hn)
    exact heq.trans (hrep n).choose_spec.2.symm
  have hstep (n : ℕ) (hn : N ≤ n) :
      op1385HiddenRecord Prod.fst (op1385Own G pl σ) (op1385Hidden G pl σ) [] (histories (n+1)) ≤
      op1385HiddenRecord Prod.fst (op1385Own G pl σ) (op1385Hidden G pl σ) [] (histories n) := by
    have hb := (op1385_next_record_bound G pl σ (π n).source_node (π n).source_state
      (hreach n) (π n) (hlegal n) rfl rfl (hchosen n)).2
    rw [← (hnext n).1, ← (hnext n).2, ← (hrep (n+1)).choose_spec.2, hrecord n hn] at hb
    exact hb
  exact prioritized_borel_eventual_hidden_shadow Prod.fst (op1385Own G pl σ) (op1385Hidden G pl σ)
    (op1385Policy G pl σ) (op1385Forced G pl σ) histories actual N hcompat hdir
    (fun n _ => hext n) hrecord hstep

lemma op1385_play_nodes {Q : Type} {k : ℕ} (π : ℕ → TreeGameEdge Q k)
    (hinit : (π 0).source_node = [])
    (hnext : ∀ n, (π (n+1)).source_node = (π n).source_node ++ [(π n).dir]) :
    ∀ n, (π n).source_node = op1385FnPrefix (fun i => (π i).dir) n := by
  intro n
  induction n with
  | zero => simpa [op1385FnPrefix] using hinit
  | succ n ih =>
    rw [hnext n, op1385_fn_prefix_succ, ih]

theorem prioritized_borel_finite_hidden_opponent_choices_positional {Q : Type} {k : ℕ} (G : PrioritizedBorelGame Q k) (pl : BorelGamePlayer) (M : Type) (σ : FiniteMemoryStrategy G pl M) (hwin : PrioritizedBorelStrategyWins G pl σ) (hfinite : ∀ π : ℕ → TreeGameEdge Q k, (∀ n, π n ∈ G.edges) → (π 0).source_node = [] ∧ (π 0).source_state = G.init_state → (∀ n, (π (n+1)).source_node = (π n).source_node ++ [(π n).dir] ∧ (π (n+1)).source_state = (π n).target_state) → ∃ N, ∀ n ≥ N, G.owner ((π n).source_node, (π n).source_state) = pl ∨ ∀ e ∈ G.edges, e.source_node = (π n).source_node → e.source_state = (π n).source_state → e.dir = (π n).dir → e = π n) : ∃ τ : FiniteMemoryStrategy G pl Unit, PrioritizedBorelStrategyWins G pl τ := by
  classical
  obtain ⟨ord, hwf⟩ := exists_wellFoundedLT (List (op1385Sig Q k))
  letI : LinearOrder (List (op1385Sig Q k)) := ord
  letI : WellFoundedLT (List (op1385Sig Q k)) := hwf
  let τ := op1385Positional G pl σ
  refine ⟨τ, ?_⟩
  unfold PrioritizedBorelStrategyWins
  intro π hlegal hinit hnext hmem
  obtain ⟨mem, hm0, hmu, hchoice⟩ := hmem
  have hfollow : ∀ n, G.owner ((π n).source_node, (π n).source_state) = pl →
      π n = (op1385Positional G pl σ).choice () (π n).source_node (π n).source_state := by
    intro n hn
    have hm : mem n = () := Subsingleton.elim _ _
    simpa [hm, τ] using hchoice n hn
  obtain ⟨N, hnonhidden⟩ := hfinite π hlegal hinit hnext
  obtain ⟨K, hKN, hstable⟩ :=
    op1385_positional_representatives_stabilize G pl σ π hlegal hinit hnext hfollow N hnonhidden
  let histories : ℕ → List (op1385Sig Q k) := fun n =>
    op1385Representative G pl σ (π n).source_node (π n).source_state
  let actual : ℕ → op1385Sig Q k := fun n => op1385EdgeSig (π n)
  have hreach := op1385_positional_reachable G pl σ π hlegal hinit hnext hfollow
  have hrep (n : ℕ) : ∃ m, PrioritizedBorelStrategyHistory G pl σ (histories n) m
      (π n).source_node (π n).source_state := by
    obtain ⟨m, hh, _⟩ := op1385_representative_spec G pl σ _ _ (hreach n)
    exact ⟨m, hh⟩
  have hnode (n : ℕ) : (histories n).map Prod.fst = (π n).source_node := by
    obtain ⟨m, hh⟩ := hrep n
    have heval := op1385_eval_history G pl σ (histories n) m _ _ hh
    simpa [heval] using (op1385_eval_node G pl σ (histories n)).symm
  have hnodes := op1385_play_nodes π hinit.1 (fun n => (hnext n).1)
  have hlen (n : ℕ) : (histories n).length = n := by
    have h := congrArg List.length (hnode n)
    simpa [hnodes, op1385FnPrefix] using h
  have hvis (n : ℕ) : (histories n).map Prod.fst =
      List.ofFn (fun i : Fin n => Prod.fst (actual i)) := by
    simpa [actual, op1385EdgeSig, op1385FnPrefix] using (hnode n).trans (hnodes n)
  obtain ⟨f, hprefix, htail, hvisall⟩ :=
    op1385_nested_histories_visible_shadow Prod.fst histories actual K hlen hvis hstable
  have hrepall (n : ℕ) : ∃ m v q, PrioritizedBorelStrategyHistory G pl σ (histories n) m v q := by
    obtain ⟨m, hh⟩ := hrep n
    exact ⟨m, _, _, hh⟩
  have hall := op1385_all_shadow_prefixes G pl σ histories f K hrepall hprefix
  have hshadow := op1385_shadow_play_of_histories G pl σ f (by simpa [op1385FnPrefix] using hall)
  let ρ := op1385ShadowEdge G pl σ f
  have hw := hwin ρ hshadow.1 hshadow.2.1 hshadow.2.2.1 hshadow.2.2.2
  have hdir : ∀ n, (π n).dir = (ρ n).dir := by
    intro n
    simpa [ρ, op1385ShadowEdge, op1385MakeEdge, actual, op1385EdgeSig] using (hvisall n).symm
  have hprio : ∀ᶠ n in Filter.atTop, (π n).prio = (ρ n).prio := by
    apply Filter.eventually_atTop.mpr
    refine ⟨K, ?_⟩
    intro n hn
    simpa [ρ, op1385ShadowEdge, op1385MakeEdge, actual, op1385EdgeSig] using
      congrArg (fun a : op1385Sig Q k => a.2.2) (htail n hn).symm
  have hequiv := prioritized_borel_payoff_tail_congr G π ρ hdir hprio
  cases pl with
  | Eve => exact hequiv.mpr hw
  | Adam => exact fun h => hw (hequiv.mp h)
