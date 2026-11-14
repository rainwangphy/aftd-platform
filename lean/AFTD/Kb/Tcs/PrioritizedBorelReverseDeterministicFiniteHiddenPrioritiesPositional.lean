import AFTD.Prelude
import AFTD.Kb.Tcs.PrioritizedBorelGame
import AFTD.Kb.Tcs.FiniteMemoryStrategy
import AFTD.Kb.Tcs.PrioritizedBorelStrategyWins
import AFTD.Kb.Tcs.TreeGameEdge
import AFTD.Kb.Tcs.BorelGamePlayer
import AFTD.Kb.Tcs.PrioritizedBorelReverseStateHistoriesUnique
import AFTD.Kb.Tcs.PrioritizedBorelFiniteHiddenOpponentChoicesPositional
import AFTD.Kb.Tcs.PrioritizedBorelStrategyHistory
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.PrioritizedBorelEventualHiddenShadow
import AFTD.Kb.Tcs.PrioritizedBorelPayoffTailCongr

/-!
# prioritized_borel_reverse_deterministic_finite_hidden_priorities_positional

Topic: automata   Node: f046229ccccf

Provenance: original. Related work: Reverse state reconstruction and eventual hidden-priority compression related to arXiv:2611.10136, Conjecture 19.

Consider a prioritized tree game. Assume that any two legal edges at the same source node with the same direction and target state have the same source state. Fix a player and a winning strategy for that player, allowing any memory type. Suppose that for every legal infinite play there is an index N such that, at each opponent-controlled position from N onward, the edge actually played is the only legal edge with that source node, source state, direction, and target state. Then that same player has a winning strategy whose memory type is Unit. The hypothesis is relative to the edge actually played: it allows other edges with a different direction or target state.
-/

def rdhHiddenStep {A B : Type} (vis : A → B) (own : List A → Bool)
    (hidden : List A → B → Bool) (policy : List A → A)
    (forced : List A → B → A) (hist : List A) (a : A) : Prop :=
  if own hist then a = policy hist
  else if hidden hist (vis a) then True else a = forced hist (vis a)

def rdhHiddenCompatible {A B : Type} (vis : A → B) (own : List A → Bool)
    (hidden : List A → B → Bool) (policy : List A → A)
    (forced : List A → B → A) : List A → List A → Prop
  | _, [] => True
  | hist, a :: rest =>
    rdhHiddenStep vis own hidden policy forced hist a ∧
      rdhHiddenCompatible vis own hidden policy forced (hist ++ [a]) rest

def rdhHiddenRecord {A B : Type} (vis : A → B) (own : List A → Bool)
    (hidden : List A → B → Bool) : List A → List A → List A
  | _, [] => []
  | hist, a :: rest =>
    if !own hist && hidden hist (vis a) then
      a :: rdhHiddenRecord vis own hidden (hist ++ [a]) rest
    else rdhHiddenRecord vis own hidden (hist ++ [a]) rest

def rdhHiddenReplay {A B : Type} [DecidableEq B] (vis : A → B) (own : List A → Bool)
    (hidden : List A → B → Bool) (policy : List A → A)
    (forced : List A → B → A) : List A → List B → List A → Option (List A × List A)
  | hist, [], record => some (hist, record)
  | hist, b :: bs, record =>
    if own hist then
      let a := policy hist
      if vis a = b then rdhHiddenReplay vis own hidden policy forced (hist ++ [a]) bs record
      else none
    else if hidden hist b then
      match record with
      | [] => none
      | a :: tail =>
        if vis a = b then rdhHiddenReplay vis own hidden policy forced (hist ++ [a]) bs tail
        else none
    else
      let a := forced hist b
      if vis a = b then rdhHiddenReplay vis own hidden policy forced (hist ++ [a]) bs record
      else none

theorem rdh_hidden_replay_recovers {A B : Type} [DecidableEq B] (vis : A → B) (own : List A → Bool)
    (hidden : List A → B → Bool) (policy : List A → A)
    (forced : List A → B → A) (hist xs : List A)
    (h : rdhHiddenCompatible vis own hidden policy forced hist xs) :
    rdhHiddenReplay vis own hidden policy forced hist (xs.map vis)
      (rdhHiddenRecord vis own hidden hist xs) = some (hist ++ xs, []) := by
  induction xs generalizing hist with
  | nil => simp [rdhHiddenRecord, rdhHiddenReplay]
  | cons a xs ih =>
    simp only [rdhHiddenCompatible] at h
    cases ho : own hist <;> cases hb : hidden hist (vis a)
    · have ha' : a = forced hist (vis a) := by simpa [rdhHiddenStep, ho, hb] using h.1
      have ha : forced hist (vis a) = a := ha'.symm
      simpa [rdhHiddenRecord, rdhHiddenReplay, ho, hb, ha, List.append_assoc] using
        ih (hist ++ [a]) h.2
    · simpa [rdhHiddenRecord, rdhHiddenReplay, ho, hb, List.append_assoc] using
        ih (hist ++ [a]) h.2
    · have ha : a = policy hist := by simpa [rdhHiddenStep, ho, hb] using h.1
      subst a
      simpa [rdhHiddenRecord, rdhHiddenReplay, ho, hb, List.append_assoc] using
        ih (hist ++ [policy hist]) h.2
    · have ha : a = policy hist := by simpa [rdhHiddenStep, ho, hb] using h.1
      subst a
      simpa [rdhHiddenRecord, rdhHiddenReplay, ho, hb, List.append_assoc] using
        ih (hist ++ [policy hist]) h.2

theorem rdh_hidden_record_injective {A B : Type} [DecidableEq B] (vis : A → B) (own : List A → Bool)
    (hidden : List A → B → Bool) (policy : List A → A)
    (forced : List A → B → A) (hist xs ys : List A)
    (hx : rdhHiddenCompatible vis own hidden policy forced hist xs)
    (hy : rdhHiddenCompatible vis own hidden policy forced hist ys)
    (hvis : xs.map vis = ys.map vis)
    (hrecord : rdhHiddenRecord vis own hidden hist xs =
      rdhHiddenRecord vis own hidden hist ys) : xs = ys := by
  have hx' := rdh_hidden_replay_recovers vis own hidden policy forced hist xs hx
  have hy' := rdh_hidden_replay_recovers vis own hidden policy forced hist ys hy
  rw [hvis, hrecord] at hx'
  have h := hx'.symm.trans hy'
  exact List.append_cancel_left (congrArg Prod.fst (Option.some.inj h))

theorem rdh_hidden_compatible_snoc {A B : Type} (vis : A → B) (own : List A → Bool)
    (hidden : List A → B → Bool) (policy : List A → A)
    (forced : List A → B → A) (hist xs : List A) (a : A) :
    rdhHiddenCompatible vis own hidden policy forced hist (xs ++ [a]) ↔
      rdhHiddenCompatible vis own hidden policy forced hist xs ∧
      rdhHiddenStep vis own hidden policy forced (hist ++ xs) a := by
  induction xs generalizing hist with
  | nil => simp [rdhHiddenCompatible]
  | cons x xs ih =>
    simp [rdhHiddenCompatible, ih, List.append_assoc, and_assoc]

theorem rdh_hidden_record_snoc {A B : Type} (vis : A → B) (own : List A → Bool)
    (hidden : List A → B → Bool) (hist xs : List A) (a : A) :
    rdhHiddenRecord vis own hidden hist (xs ++ [a]) =
      rdhHiddenRecord vis own hidden hist xs ++
        (if !own (hist ++ xs) && hidden (hist ++ xs) (vis a) then [a] else []) := by
  induction xs generalizing hist with
  | nil => simp [rdhHiddenRecord]
  | cons x xs ih =>
    cases hb : (!own hist && hidden hist (vis x)) <;>
      simp [rdhHiddenRecord, hb, ih, List.append_assoc]

theorem rdh_eventual_hidden_shadow {A B : Type} [LinearOrder (List A)]
    [WellFoundedLT (List A)] (vis : A → B) (own : List A → Bool)
    (hidden : List A → B → Bool) (policy : List A → A)
    (forced : List A → B → A) (histories : ℕ → List A) (actual : ℕ → A)
    (N : ℕ)
    (hcompat : ∀ n, rdhHiddenCompatible vis own hidden policy forced [] (histories n))
    (hdir : ∀ n, (histories (n+1)).map vis = (histories n).map vis ++ [vis (actual n)])
    (hext : ∀ n ≥ N, rdhHiddenCompatible vis own hidden policy forced []
      (histories n ++ [actual n]))
    (hrecord : ∀ n ≥ N, rdhHiddenRecord vis own hidden [] (histories n ++ [actual n]) =
      rdhHiddenRecord vis own hidden [] (histories n))
    (hstep : ∀ n ≥ N, rdhHiddenRecord vis own hidden [] (histories (n+1)) ≤
      rdhHiddenRecord vis own hidden [] (histories n)) :
    ∃ K ≥ N, ∀ n ≥ K, histories (n+1) = histories n ++ [actual n] := by
  classical
  let rank : ℕ → List A := fun n => rdhHiddenRecord vis own hidden [] (histories n)
  obtain ⟨K, hKN, hstable⟩ := op1385_eventually_antitone_well_order_stabilizes rank N hstep
  refine ⟨K, hKN, ?_⟩
  intro n hn
  have hnN : N ≤ n := le_trans hKN hn
  have hrec : rdhHiddenRecord vis own hidden [] (histories (n+1)) =
      rdhHiddenRecord vis own hidden [] (histories n ++ [actual n]) := by
    rw [hrecord n hnN]
    exact (hstable (n+1) (by omega)).trans (hstable n hn).symm
  apply rdh_hidden_record_injective vis own hidden policy forced []
    (histories (n+1)) (histories n ++ [actual n]) (hcompat (n+1)) (hext n hnN)
  · simpa using hdir n
  · exact hrec

def rdhVis {Q : Type} {k : ℕ} (a : op1385Sig Q k) : Bool × Q := (a.1, a.2.1)

noncomputable def rdhHidden {Q M : Type} {k : ℕ} (G : PrioritizedBorelGame Q k)
    (pl : BorelGamePlayer) (σ : FiniteMemoryStrategy G pl M)
    (h : List (op1385Sig Q k)) (b : Bool × Q) : Bool := by
  classical
  let st := op1385Eval G pl σ h
  exact decide (∃ e ∈ G.edges, ∃ e' ∈ G.edges,
    e.source_node = st.2.1 ∧ e.source_state = st.2.2 ∧ e.dir = b.1 ∧ e.target_state = b.2 ∧
    e'.source_node = st.2.1 ∧ e'.source_state = st.2.2 ∧ e'.dir = b.1 ∧
      e'.target_state = b.2 ∧ e ≠ e')

noncomputable def rdhForced {Q M : Type} {k : ℕ} (G : PrioritizedBorelGame Q k)
    (pl : BorelGamePlayer) (σ : FiniteMemoryStrategy G pl M)
    (h : List (op1385Sig Q k)) (b : Bool × Q) : op1385Sig Q k := by
  classical
  let st := op1385Eval G pl σ h
  exact if hex : ∃ e ∈ G.edges,
      e.source_node = st.2.1 ∧ e.source_state = st.2.2 ∧ e.dir = b.1 ∧ e.target_state = b.2
    then op1385EdgeSig (Classical.choose hex)
    else op1385EdgeSig (σ.choice st.1 st.2.1 st.2.2)

lemma rdh_hidden_false_unique {Q M : Type} {k : ℕ} (G : PrioritizedBorelGame Q k)
    (pl : BorelGamePlayer) (σ : FiniteMemoryStrategy G pl M)
    (h : List (op1385Sig Q k)) (b : Bool × Q)
    (e e' : TreeGameEdge Q k) (he : e ∈ G.edges) (he' : e' ∈ G.edges)
    (hv : e.source_node = (op1385Eval G pl σ h).2.1)
    (hq : e.source_state = (op1385Eval G pl σ h).2.2) (hd : e.dir = b.1) (ht : e.target_state = b.2)
    (hv' : e'.source_node = (op1385Eval G pl σ h).2.1)
    (hq' : e'.source_state = (op1385Eval G pl σ h).2.2) (hd' : e'.dir = b.1)
    (ht' : e'.target_state = b.2)
    (hhidden : rdhHidden G pl σ h b = false) : e = e' := by
  classical
  have hn : ¬ ∃ a ∈ G.edges, ∃ a' ∈ G.edges,
      a.source_node = (op1385Eval G pl σ h).2.1 ∧
      a.source_state = (op1385Eval G pl σ h).2.2 ∧ a.dir = b.1 ∧ a.target_state = b.2 ∧
      a'.source_node = (op1385Eval G pl σ h).2.1 ∧
      a'.source_state = (op1385Eval G pl σ h).2.2 ∧ a'.dir = b.1 ∧
        a'.target_state = b.2 ∧ a ≠ a' := by
    simpa [rdhHidden] using hhidden
  by_contra hne
  exact hn ⟨e, he, e', he', hv, hq, hd, ht, hv', hq', hd', ht', hne⟩

lemma rdh_forced_eq {Q M : Type} {k : ℕ} (G : PrioritizedBorelGame Q k)
    (pl : BorelGamePlayer) (σ : FiniteMemoryStrategy G pl M)
    (h : List (op1385Sig Q k)) (e : TreeGameEdge Q k) (he : e ∈ G.edges)
    (hv : e.source_node = (op1385Eval G pl σ h).2.1)
    (hq : e.source_state = (op1385Eval G pl σ h).2.2)
    (hhidden : rdhHidden G pl σ h (e.dir, e.target_state) = false) :
    rdhForced G pl σ h (e.dir, e.target_state) = op1385EdgeSig e := by
  classical
  have hex : ∃ a ∈ G.edges,
      a.source_node = (op1385Eval G pl σ h).2.1 ∧
      a.source_state = (op1385Eval G pl σ h).2.2 ∧ a.dir = (e.dir, e.target_state).1 ∧
        a.target_state = (e.dir, e.target_state).2 :=
    ⟨e, he, hv, hq, rfl, rfl⟩
  have hs := Classical.choose_spec hex
  have hsame : Classical.choose hex = e :=
    rdh_hidden_false_unique G pl σ h (e.dir, e.target_state) (Classical.choose hex) e
      hs.1 he hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2 hv hq rfl rfl hhidden
  unfold rdhForced
  simp only [dif_pos hex, hsame]

theorem rdh_history_hidden_compatible {Q M : Type} {k : ℕ}
    (G : PrioritizedBorelGame Q k) (pl : BorelGamePlayer) (σ : FiniteMemoryStrategy G pl M)
    (h : List (op1385Sig Q k)) (m : M) (v : List Bool) (q : Q)
    (hh : PrioritizedBorelStrategyHistory G pl σ h m v q) :
    rdhHiddenCompatible rdhVis (op1385Own G pl σ) (rdhHidden G pl σ)
      (op1385Policy G pl σ) (rdhForced G pl σ) [] h := by
  classical
  induction hh with
  | root => trivial
  | @step h m v q e hh he hnode hstate hchoice ih =>
    apply (rdh_hidden_compatible_snoc rdhVis (op1385Own G pl σ)
      (rdhHidden G pl σ) (op1385Policy G pl σ) (rdhForced G pl σ)
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
      simp [rdhHiddenStep, ho, hs]
    · have ho : op1385Own G pl σ h = false := by simp [op1385Own, heval, howner]
      cases hhidden : rdhHidden G pl σ h (e.dir, e.target_state) with
      | true => simp [rdhHiddenStep, ho, op1385EdgeSig, rdhVis, hhidden]
      | false =>
        have hf := rdh_forced_eq G pl σ h e he hnode' hstate' hhidden
        simpa [rdhHiddenStep, ho, op1385EdgeSig, rdhVis, hhidden] using hf.symm

def rdhReachableRecords {Q M : Type} {k : ℕ} (G : PrioritizedBorelGame Q k)
    (pl : BorelGamePlayer) (σ : FiniteMemoryStrategy G pl M)
    (v : List Bool) (q : Q) : Set (List (op1385Sig Q k)) :=
  {r | ∃ h m, PrioritizedBorelStrategyHistory G pl σ h m v q ∧
    rdhHiddenRecord rdhVis (op1385Own G pl σ) (rdhHidden G pl σ) [] h = r}

noncomputable def rdhBestRecord {Q M : Type} {k : ℕ}
    [LinearOrder (List (op1385Sig Q k))] [WellFoundedLT (List (op1385Sig Q k))]
    (G : PrioritizedBorelGame Q k) (pl : BorelGamePlayer) (σ : FiniteMemoryStrategy G pl M)
    (v : List Bool) (q : Q) : List (op1385Sig Q k) := by
  classical
  let S := rdhReachableRecords G pl σ v q
  exact if hs : S.Nonempty then Classical.choose (wellFounded_lt.has_min S hs) else []

lemma rdh_best_record_spec {Q M : Type} {k : ℕ}
    [LinearOrder (List (op1385Sig Q k))] [WellFoundedLT (List (op1385Sig Q k))]
    (G : PrioritizedBorelGame Q k) (pl : BorelGamePlayer) (σ : FiniteMemoryStrategy G pl M)
    (v : List Bool) (q : Q) (hs : (rdhReachableRecords G pl σ v q).Nonempty) :
    rdhBestRecord G pl σ v q ∈ rdhReachableRecords G pl σ v q ∧
      ∀ r ∈ rdhReachableRecords G pl σ v q, rdhBestRecord G pl σ v q ≤ r := by
  classical
  have hmin := Classical.choose_spec (wellFounded_lt.has_min (rdhReachableRecords G pl σ v q) hs)
  have hbest : rdhBestRecord G pl σ v q =
      Classical.choose (wellFounded_lt.has_min (rdhReachableRecords G pl σ v q) hs) := by
    simp [rdhBestRecord, hs]
  rw [hbest]
  refine ⟨hmin.1, ?_⟩
  intro r hr
  exact le_of_not_gt (hmin.2 r hr)

noncomputable def rdhRepresentative {Q M : Type} {k : ℕ}
    [LinearOrder (List (op1385Sig Q k))] [WellFoundedLT (List (op1385Sig Q k))]
    (G : PrioritizedBorelGame Q k) (pl : BorelGamePlayer) (σ : FiniteMemoryStrategy G pl M)
    (v : List Bool) (q : Q) : List (op1385Sig Q k) := by
  classical
  let S := rdhReachableRecords G pl σ v q
  exact if hs : S.Nonempty then
    Classical.choose ((rdh_best_record_spec G pl σ v q hs).1) else []

lemma rdh_representative_spec {Q M : Type} {k : ℕ}
    [LinearOrder (List (op1385Sig Q k))] [WellFoundedLT (List (op1385Sig Q k))]
    (G : PrioritizedBorelGame Q k) (pl : BorelGamePlayer) (σ : FiniteMemoryStrategy G pl M)
    (v : List Bool) (q : Q) (hs : (rdhReachableRecords G pl σ v q).Nonempty) :
    ∃ m, PrioritizedBorelStrategyHistory G pl σ (rdhRepresentative G pl σ v q) m v q ∧
      rdhHiddenRecord rdhVis (op1385Own G pl σ) (rdhHidden G pl σ) []
        (rdhRepresentative G pl σ v q) = rdhBestRecord G pl σ v q := by
  classical
  have hmem := (rdh_best_record_spec G pl σ v q hs).1
  have hrep : rdhRepresentative G pl σ v q = Classical.choose hmem := by
    simp [rdhRepresentative, hs]
  rw [hrep]
  exact Classical.choose_spec hmem

noncomputable def rdhPositional {Q M : Type} {k : ℕ}
    [LinearOrder (List (op1385Sig Q k))] [WellFoundedLT (List (op1385Sig Q k))]
    (G : PrioritizedBorelGame Q k) (pl : BorelGamePlayer) (σ : FiniteMemoryStrategy G pl M) :
    FiniteMemoryStrategy G pl Unit where
  init_mem := ()
  update := fun _ _ => ()
  choice := fun _ v q => by
    classical
    exact if (rdhReachableRecords G pl σ v q).Nonempty then
      σ.choice (op1385Eval G pl σ (rdhRepresentative G pl σ v q)).1 v q
    else op1385Fallback G v q
  choice_edge := by
    classical
    intro _ v q howner
    split
    · exact σ.choice_edge _ v q howner
    · exact op1385_fallback_spec G v q

lemma rdh_representative_extend {Q M : Type} {k : ℕ}
    [LinearOrder (List (op1385Sig Q k))] [WellFoundedLT (List (op1385Sig Q k))]
    (G : PrioritizedBorelGame Q k) (pl : BorelGamePlayer) (σ : FiniteMemoryStrategy G pl M)
    (v : List Bool) (q : Q) (hs : (rdhReachableRecords G pl σ v q).Nonempty)
    (e : TreeGameEdge Q k) (he : e ∈ G.edges) (hv : e.source_node = v) (hq : e.source_state = q)
    (hchosen : G.owner (v, q) = pl →
      e = σ.choice (op1385Eval G pl σ (rdhRepresentative G pl σ v q)).1 v q) :
    ∃ m, PrioritizedBorelStrategyHistory G pl σ
      (rdhRepresentative G pl σ v q ++ [op1385EdgeSig e]) m (v ++ [e.dir]) e.target_state := by
  obtain ⟨m, hh, _⟩ := rdh_representative_spec G pl σ v q hs
  have heval := op1385_eval_history G pl σ _ m v q hh
  refine ⟨σ.update m e, PrioritizedBorelStrategyHistory.step e hh he hv hq ?_⟩
  intro howner
  simpa [heval] using hchosen howner

lemma rdh_next_record_bound {Q M : Type} {k : ℕ}
    [LinearOrder (List (op1385Sig Q k))] [WellFoundedLT (List (op1385Sig Q k))]
    (G : PrioritizedBorelGame Q k) (pl : BorelGamePlayer) (σ : FiniteMemoryStrategy G pl M)
    (v : List Bool) (q : Q) (hs : (rdhReachableRecords G pl σ v q).Nonempty)
    (e : TreeGameEdge Q k) (he : e ∈ G.edges) (hv : e.source_node = v) (hq : e.source_state = q)
    (hchosen : G.owner (v, q) = pl →
      e = σ.choice (op1385Eval G pl σ (rdhRepresentative G pl σ v q)).1 v q) :
    (rdhReachableRecords G pl σ (v ++ [e.dir]) e.target_state).Nonempty ∧
    rdhBestRecord G pl σ (v ++ [e.dir]) e.target_state ≤
      rdhHiddenRecord rdhVis (op1385Own G pl σ) (rdhHidden G pl σ) []
        (rdhRepresentative G pl σ v q ++ [op1385EdgeSig e]) := by
  obtain ⟨m, hh⟩ := rdh_representative_extend G pl σ v q hs e he hv hq hchosen
  let r := rdhHiddenRecord rdhVis (op1385Own G pl σ) (rdhHidden G pl σ) []
    (rdhRepresentative G pl σ v q ++ [op1385EdgeSig e])
  have hr : r ∈ rdhReachableRecords G pl σ (v ++ [e.dir]) e.target_state := by
    exact ⟨_, m, hh, rfl⟩
  have hne : (rdhReachableRecords G pl σ (v ++ [e.dir]) e.target_state).Nonempty := ⟨r, hr⟩
  exact ⟨hne, (rdh_best_record_spec G pl σ (v ++ [e.dir]) e.target_state hne).2 r hr⟩

theorem rdh_positional_reachable {Q M : Type} {k : ℕ}
    [LinearOrder (List (op1385Sig Q k))] [WellFoundedLT (List (op1385Sig Q k))]
    (G : PrioritizedBorelGame Q k) (pl : BorelGamePlayer) (σ : FiniteMemoryStrategy G pl M)
    (π : ℕ → TreeGameEdge Q k) (hlegal : ∀ n, π n ∈ G.edges)
    (hinit : (π 0).source_node = [] ∧ (π 0).source_state = G.init_state)
    (hnext : ∀ n, (π (n+1)).source_node = (π n).source_node ++ [(π n).dir] ∧
      (π (n+1)).source_state = (π n).target_state)
    (hfollow : ∀ n, G.owner ((π n).source_node, (π n).source_state) = pl →
      π n = (rdhPositional G pl σ).choice () (π n).source_node (π n).source_state) :
    ∀ n, (rdhReachableRecords G pl σ (π n).source_node (π n).source_state).Nonempty := by
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
          (rdhRepresentative G pl σ (π n).source_node (π n).source_state)).1
          (π n).source_node (π n).source_state := by
      intro howner
      simpa [rdhPositional, ih] using hfollow n howner
    have hbound := rdh_next_record_bound G pl σ (π n).source_node (π n).source_state
      ih (π n) (hlegal n) rfl rfl hc
    rw [(hnext n).1, (hnext n).2]
    exact hbound.1

lemma rdh_extension_record_unchanged {Q M : Type} {k : ℕ}
    [LinearOrder (List (op1385Sig Q k))] [WellFoundedLT (List (op1385Sig Q k))]
    (G : PrioritizedBorelGame Q k) (pl : BorelGamePlayer) (σ : FiniteMemoryStrategy G pl M)
    (v : List Bool) (q : Q) (hs : (rdhReachableRecords G pl σ v q).Nonempty)
    (e : TreeGameEdge Q k) (he : e ∈ G.edges) (hv : e.source_node = v) (hq : e.source_state = q)
    (hnonhidden : G.owner (v, q) = pl ∨ ∀ e' ∈ G.edges,
      e'.source_node = v → e'.source_state = q → e'.dir = e.dir →
        e'.target_state = e.target_state → e' = e) :
    rdhHiddenRecord rdhVis (op1385Own G pl σ) (rdhHidden G pl σ) []
      (rdhRepresentative G pl σ v q ++ [op1385EdgeSig e]) =
    rdhBestRecord G pl σ v q := by
  classical
  obtain ⟨m, hh, hrec⟩ := rdh_representative_spec G pl σ v q hs
  have heval := op1385_eval_history G pl σ _ m v q hh
  have hstore : (!op1385Own G pl σ (rdhRepresentative G pl σ v q) &&
      rdhHidden G pl σ (rdhRepresentative G pl σ v q) (e.dir, e.target_state)) = false := by
    rcases hnonhidden with howner | hunique
    · simp [op1385Own, heval, howner]
    · have hn : ¬ ∃ a ∈ G.edges, ∃ a' ∈ G.edges,
          a.source_node = v ∧ a.source_state = q ∧ a.dir = e.dir ∧ a.target_state = e.target_state ∧
          a'.source_node = v ∧ a'.source_state = q ∧ a'.dir = e.dir ∧
            a'.target_state = e.target_state ∧ a ≠ a' := by
        rintro ⟨a, ha, a', ha', hav, haq, had, hat, hav', haq', had', hat', hne⟩
        exact hne ((hunique a ha hav haq had hat).trans (hunique a' ha' hav' haq' had' hat').symm)
      have hhfalse : rdhHidden G pl σ (rdhRepresentative G pl σ v q)
          (e.dir, e.target_state) = false := by
        simpa [rdhHidden, heval] using hn
      simp [hhfalse]
  rw [rdh_hidden_record_snoc]
  simpa [op1385EdgeSig, rdhVis, hstore] using hrec

theorem rdh_history_vis_unique {Q M : Type} {k : ℕ} (G : PrioritizedBorelGame Q k)
    (pl : BorelGamePlayer) (σ : FiniteMemoryStrategy G pl M)
    (hreverse : ∀ e ∈ G.edges, ∀ e' ∈ G.edges, e.source_node = e'.source_node →
      e.dir = e'.dir → e.target_state = e'.target_state → e.source_state = e'.source_state)
    (h : List (op1385Sig Q k)) (m : M) (v : List Bool) (q : Q)
    (hh : PrioritizedBorelStrategyHistory G pl σ h m v q) :
    ∀ (h' : List (op1385Sig Q k)) (m' : M), PrioritizedBorelStrategyHistory G pl σ h' m' v q →
      h.map rdhVis = h'.map rdhVis := by
  induction hh with
  | root =>
    intro h' m' hh'
    have hn := op1385_eval_node G pl σ h'
    rw [op1385_eval_history G pl σ h' m' [] G.init_state hh'] at hn
    have hl := congrArg List.length hn
    simp only [List.length_nil, List.length_map] at hl
    have : h' = [] := List.eq_nil_of_length_eq_zero hl.symm
    subst this
    rfl
  | @step h m v q e hh he hv hq hc ih =>
    intro h' m' hh'
    have hn := op1385_eval_node G pl σ h'
    rw [op1385_eval_history G pl σ h' m' _ _ hh'] at hn
    obtain ⟨h0, a, rfl⟩ : ∃ h0 a, h' = h0 ++ [a] := by
      rcases List.eq_nil_or_concat h' with h0 | ⟨L, b, hL⟩
      · subst h0
        simp at hn
      · exact ⟨L, b, by simpa using hL⟩
    obtain ⟨m₀, v₀, q₀, e', hh0, he', hv', hq', _, ha, _, hvv, hqq⟩ :=
      op1385_history_snoc_inv G pl σ _ m' _ _ hh' h0 a rfl
    obtain ⟨hv0, hd⟩ := List.append_inj' hvv rfl
    have hd' : e.dir = e'.dir := by simpa using hd
    have hs := hreverse e he e' he' (hv.trans (hv0.trans hv'.symm)) hd' hqq
    have hq0 : q = q₀ := hq.symm.trans (hs.trans hq')
    subst hv0
    subst hq0
    have hih := ih h0 m₀ hh0
    rw [← ha]
    simp [List.map_append, hih, rdhVis, op1385EdgeSig, hd', hqq]

theorem rdh_positional_representatives_stabilize {Q M : Type} {k : ℕ}
    [LinearOrder (List (op1385Sig Q k))] [WellFoundedLT (List (op1385Sig Q k))]
    (G : PrioritizedBorelGame Q k) (pl : BorelGamePlayer) (σ : FiniteMemoryStrategy G pl M)
    (π : ℕ → TreeGameEdge Q k) (hlegal : ∀ n, π n ∈ G.edges)
    (hinit : (π 0).source_node = [] ∧ (π 0).source_state = G.init_state)
    (hnext : ∀ n, (π (n+1)).source_node = (π n).source_node ++ [(π n).dir] ∧
      (π (n+1)).source_state = (π n).target_state)
    (hfollow : ∀ n, G.owner ((π n).source_node, (π n).source_state) = pl →
      π n = (rdhPositional G pl σ).choice () (π n).source_node (π n).source_state)
    (hreverse : ∀ e ∈ G.edges, ∀ e' ∈ G.edges, e.source_node = e'.source_node →
      e.dir = e'.dir → e.target_state = e'.target_state → e.source_state = e'.source_state)
    (N : ℕ) (hnonhidden : ∀ n ≥ N, G.owner ((π n).source_node, (π n).source_state) = pl ∨
      ∀ e ∈ G.edges, e.source_node = (π n).source_node →
        e.source_state = (π n).source_state → e.dir = (π n).dir →
          e.target_state = (π n).target_state → e = π n) :
    ∃ K ≥ N, ∀ n ≥ K,
      rdhRepresentative G pl σ (π (n+1)).source_node (π (n+1)).source_state =
      rdhRepresentative G pl σ (π n).source_node (π n).source_state ++ [op1385EdgeSig (π n)] := by
  classical
  let histories : ℕ → List (op1385Sig Q k) := fun n =>
    rdhRepresentative G pl σ (π n).source_node (π n).source_state
  let actual : ℕ → op1385Sig Q k := fun n => op1385EdgeSig (π n)
  have hreach := rdh_positional_reachable G pl σ π hlegal hinit hnext hfollow
  have hrep (n : ℕ) : ∃ m, PrioritizedBorelStrategyHistory G pl σ (histories n) m
      (π n).source_node (π n).source_state ∧
      rdhHiddenRecord rdhVis (op1385Own G pl σ) (rdhHidden G pl σ) [] (histories n) =
        rdhBestRecord G pl σ (π n).source_node (π n).source_state :=
    rdh_representative_spec G pl σ (π n).source_node (π n).source_state (hreach n)
  have hcompat (n : ℕ) : rdhHiddenCompatible rdhVis (op1385Own G pl σ)
      (rdhHidden G pl σ) (op1385Policy G pl σ) (rdhForced G pl σ) [] (histories n) := by
    obtain ⟨m, hh, _⟩ := hrep n
    exact rdh_history_hidden_compatible G pl σ _ m _ _ hh
  have hnode (n : ℕ) : (histories n).map Prod.fst = (π n).source_node := by
    obtain ⟨m, hh, _⟩ := hrep n
    have heval := op1385_eval_history G pl σ (histories n) m _ _ hh
    simpa [heval] using (op1385_eval_node G pl σ (histories n)).symm
  have hchosen (n : ℕ) : G.owner ((π n).source_node, (π n).source_state) = pl →
      π n = σ.choice (op1385Eval G pl σ (histories n)).1
        (π n).source_node (π n).source_state := by
    intro howner
    simpa [histories, rdhPositional, hreach n] using hfollow n howner
  have hext (n : ℕ) : rdhHiddenCompatible rdhVis (op1385Own G pl σ)
      (rdhHidden G pl σ) (op1385Policy G pl σ) (rdhForced G pl σ) []
      (histories n ++ [actual n]) := by
    obtain ⟨m, hh⟩ := rdh_representative_extend G pl σ (π n).source_node (π n).source_state
      (hreach n) (π n) (hlegal n) rfl rfl (hchosen n)
    exact rdh_history_hidden_compatible G pl σ _ m _ _ hh
  have hdir (n : ℕ) : (histories (n+1)).map rdhVis =
      (histories n).map rdhVis ++ [rdhVis (actual n)] := by
    obtain ⟨m, hh⟩ := rdh_representative_extend G pl σ (π n).source_node (π n).source_state
      (hreach n) (π n) (hlegal n) rfl rfl (hchosen n)
    obtain ⟨m', hh', _⟩ := hrep (n+1)
    rw [(hnext n).1, (hnext n).2] at hh'
    have hu := rdh_history_vis_unique G pl σ hreverse _ _ _ _ hh' _ _ hh
    rw [hu, List.map_append]
    rfl
  have hrecord (n : ℕ) (hn : N ≤ n) :
      rdhHiddenRecord rdhVis (op1385Own G pl σ) (rdhHidden G pl σ) []
        (histories n ++ [actual n]) =
      rdhHiddenRecord rdhVis (op1385Own G pl σ) (rdhHidden G pl σ) [] (histories n) := by
    have heq := rdh_extension_record_unchanged G pl σ (π n).source_node (π n).source_state
      (hreach n) (π n) (hlegal n) rfl rfl (hnonhidden n hn)
    exact heq.trans (hrep n).choose_spec.2.symm
  have hstep (n : ℕ) (hn : N ≤ n) :
      rdhHiddenRecord rdhVis (op1385Own G pl σ) (rdhHidden G pl σ) [] (histories (n+1)) ≤
      rdhHiddenRecord rdhVis (op1385Own G pl σ) (rdhHidden G pl σ) [] (histories n) := by
    have hb := (rdh_next_record_bound G pl σ (π n).source_node (π n).source_state
      (hreach n) (π n) (hlegal n) rfl rfl (hchosen n)).2
    rw [← (hnext n).1, ← (hnext n).2, ← (hrep (n+1)).choose_spec.2, hrecord n hn] at hb
    exact hb
  exact rdh_eventual_hidden_shadow rdhVis (op1385Own G pl σ) (rdhHidden G pl σ)
    (op1385Policy G pl σ) (rdhForced G pl σ) histories actual N hcompat hdir
    (fun n _ => hext n) hrecord hstep

theorem prioritized_borel_reverse_deterministic_finite_hidden_priorities_positional {Q : Type} {k : ℕ} (G : PrioritizedBorelGame Q k) (pl : BorelGamePlayer) (M : Type) (σ : FiniteMemoryStrategy G pl M) (hwin : PrioritizedBorelStrategyWins G pl σ) (hreverse : ∀ e ∈ G.edges, ∀ e' ∈ G.edges, e.source_node = e'.source_node → e.dir = e'.dir → e.target_state = e'.target_state → e.source_state = e'.source_state) (hfinite : ∀ π : ℕ → TreeGameEdge Q k, (∀ n, π n ∈ G.edges) → (π 0).source_node = [] ∧ (π 0).source_state = G.init_state → (∀ n, (π (n+1)).source_node = (π n).source_node ++ [(π n).dir] ∧ (π (n+1)).source_state = (π n).target_state) → ∃ N, ∀ n ≥ N, G.owner ((π n).source_node, (π n).source_state) = pl ∨ ∀ e ∈ G.edges, e.source_node = (π n).source_node → e.source_state = (π n).source_state → e.dir = (π n).dir → e.target_state = (π n).target_state → e = π n) : ∃ τ : FiniteMemoryStrategy G pl Unit, PrioritizedBorelStrategyWins G pl τ := by
  classical
  obtain ⟨ord, hwf⟩ := exists_wellFoundedLT (List (op1385Sig Q k))
  letI : LinearOrder (List (op1385Sig Q k)) := ord
  letI : WellFoundedLT (List (op1385Sig Q k)) := hwf
  let τ := rdhPositional G pl σ
  refine ⟨τ, ?_⟩
  unfold PrioritizedBorelStrategyWins
  intro π hlegal hinit hnext hmem
  obtain ⟨mem, hm0, hmu, hchoice⟩ := hmem
  have hfollow : ∀ n, G.owner ((π n).source_node, (π n).source_state) = pl →
      π n = (rdhPositional G pl σ).choice () (π n).source_node (π n).source_state := by
    intro n hn
    have hm : mem n = () := Subsingleton.elim _ _
    simpa [hm, τ] using hchoice n hn
  obtain ⟨N, hnonhidden⟩ := hfinite π hlegal hinit hnext
  obtain ⟨K, hKN, hstable⟩ :=
    rdh_positional_representatives_stabilize G pl σ π hlegal hinit hnext hfollow hreverse N hnonhidden
  let histories : ℕ → List (op1385Sig Q k) := fun n =>
    rdhRepresentative G pl σ (π n).source_node (π n).source_state
  let actual : ℕ → op1385Sig Q k := fun n => op1385EdgeSig (π n)
  have hreach := rdh_positional_reachable G pl σ π hlegal hinit hnext hfollow
  have hrep (n : ℕ) : ∃ m, PrioritizedBorelStrategyHistory G pl σ (histories n) m
      (π n).source_node (π n).source_state := by
    obtain ⟨m, hh, _⟩ := rdh_representative_spec G pl σ _ _ (hreach n)
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
