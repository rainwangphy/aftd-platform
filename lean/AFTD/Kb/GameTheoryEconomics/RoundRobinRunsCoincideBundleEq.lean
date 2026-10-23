import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PickingSequenceOutcome
import AFTD.Kb.GameTheoryEconomics.PickingTurn
import AFTD.Kb.GameTheoryEconomics.PickingPrefixState
import AFTD.Kb.GameTheoryEconomics.RoundRobinSequence
import AFTD.Kb.Tcs.G

/-!
# round_robin_runs_coincide_bundle_eq

Topic: fair_division   Node: 5b65136486fc

Provenance: helper lemma. step towards round_robin_phi_lex_strict_increase

If two Round-Robin executions have the same set of allocated items at each turn s <= m, then both executions produce identical final bundle allocations.
-/

/-- If two picking turns starting from the same state allocate the same set of goods, they also give the same bundles. -/
lemma round_robin_runs_coincide_bundle_eq_turn_alloc_eq {N G : Type*} [DecidableEq N] [DecidableEq G]
    (st : (N → Finset G) × Finset G) (a : N) (l l' : List G)
    (h : (picking_turn l a st).2 = (picking_turn l' a st).2) :
    (picking_turn l a st).1 = (picking_turn l' a st).1 := by
  unfold picking_turn at h ⊢
  cases hl : List.find? (fun g => decide (g ∉ st.2)) l with
  | none =>
    cases hl' : List.find? (fun g => decide (g ∉ st.2)) l' with
    | none => rfl
    | some g' =>
      simp only [hl, hl'] at h
      have hg' : g' ∉ st.2 := by simpa using List.find?_some hl'
      exfalso
      apply hg'
      rw [h]
      exact Finset.mem_insert_self g' st.2
  | some g =>
    cases hl' : List.find? (fun g => decide (g ∉ st.2)) l' with
    | none =>
      simp only [hl, hl'] at h
      have hg : g ∉ st.2 := by simpa using List.find?_some hl
      exfalso
      apply hg
      rw [← h]
      exact Finset.mem_insert_self g st.2
    | some g' =>
      simp only [hl, hl'] at h ⊢
      have hg : g ∉ st.2 := by simpa using List.find?_some hl
      have hg' : g' ∉ st.2 := by simpa using List.find?_some hl'
      have hgg : g = g' := by
        have hmem : g ∈ insert g' st.2 := by
          rw [← h]
          exact Finset.mem_insert_self g st.2
        rcases Finset.mem_insert.mp hmem with h1 | h1
        · exact h1
        · exact absurd h1 hg
      subst hgg
      rfl

/-- The prefix state after k+1 turns is the k-th turn applied to the state after k turns. -/
lemma round_robin_runs_coincide_bundle_eq_prefix_succ {N G : Type*}
    [DecidableEq N] [DecidableEq G]
    {m : ℕ} (seq : List N) (rank : N → Fin m ≃ G) (k : ℕ) (a : N) (hk : seq[k]? = some a) :
    picking_prefix_state seq rank (k+1) =
      picking_turn (List.ofFn ⇑(rank a)) a (picking_prefix_state seq rank k) := by
  simp only [picking_prefix_state]
  rw [List.take_add_one, hk]
  simp [List.foldl_append]

/-- If the allocated sets of two picking-sequence runs agree after every prefix, the full prefix states agree. -/
lemma round_robin_runs_coincide_bundle_eq_fold_eq {N G : Type*}
    [DecidableEq N] [DecidableEq G] {m : ℕ}
    (seq : List N) (b b' : N → Fin m ≃ G) (hseq : seq.length ≤ m)
    (h : ∀ s ≤ m, (picking_prefix_state seq b s).2 = (picking_prefix_state seq b' s).2) :
    picking_prefix_state seq b seq.length = picking_prefix_state seq b' seq.length := by
  have key : ∀ s ≤ seq.length, picking_prefix_state seq b s = picking_prefix_state seq b' s := by
    intro s hs
    induction s with
    | zero => rfl
    | succ k ih =>
      have hk : k < seq.length := by omega
      have ihk : picking_prefix_state seq b k = picking_prefix_state seq b' k := ih (by omega)
      obtain ⟨a, ha⟩ : ∃ a, seq[k]? = some a := ⟨_, List.getElem?_eq_getElem hk⟩
      have hstep := h (k+1) (by omega)
      rw [round_robin_runs_coincide_bundle_eq_prefix_succ seq b k a ha,
          round_robin_runs_coincide_bundle_eq_prefix_succ seq b' k a ha] at hstep ⊢
      rw [ihk] at hstep ⊢
      exact Prod.ext (round_robin_runs_coincide_bundle_eq_turn_alloc_eq _ a _ _ hstep) hstep
  exact key seq.length le_rfl

/-- If two Round-Robin runs have identical allocated item sets at every step up to m, then every agent receives the exact same bundle in both runs. -/
theorem round_robin_runs_coincide_bundle_eq (n m : ℕ) [NeZero n]
    (b b' : Fin n → Fin m ≃ Fin m)
    (h : ∀ s ≤ m, (picking_prefix_state (round_robin_sequence n m) b s).2 =
                 (picking_prefix_state (round_robin_sequence n m) b' s).2) :
    picking_sequence_outcome (round_robin_sequence n m) b =
    picking_sequence_outcome (round_robin_sequence n m) b' := by
  have hlen : (round_robin_sequence n m).length = m := by
    simp [round_robin_sequence]
  have hkey := round_robin_runs_coincide_bundle_eq_fold_eq (round_robin_sequence n m) b b' (by omega) h
  have e : ∀ rank : Fin n → Fin m ≃ Fin m,
      picking_sequence_outcome (round_robin_sequence n m) rank
        = (picking_prefix_state (round_robin_sequence n m) rank (round_robin_sequence n m).length).1 := by
    intro rank
    simp only [picking_sequence_outcome, picking_prefix_state]
    rw [List.take_eq_self_iff _ |>.mpr le_rfl]
  rw [e b, e b', hkey]
