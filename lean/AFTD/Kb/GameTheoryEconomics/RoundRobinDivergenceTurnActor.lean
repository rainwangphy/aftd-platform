import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PickingTurn
import AFTD.Kb.GameTheoryEconomics.PickingPrefixState
import AFTD.Kb.GameTheoryEconomics.RoundRobinSequence
import AFTD.Kb.Tcs.G

/-!
# round_robin_divergence_turn_actor

Topic: fair_division   Node: e1fb9f40a648

Provenance: helper lemma. step towards round_robin_phi_lex_strict_increase

If only agent i deviates and the executions have identical allocated sets up to turn t but diverge at turn t + 1, then the agent acting at turn t must be agent i.
-/

theorem round_robin_divergence_turn_actor_prefix_succ {N G : Type*}
    [DecidableEq N] [DecidableEq G] {m : ℕ} (seq : List N)
    (rank : N → Fin m ≃ G) (k : ℕ) (a : N) (hk : seq[k]? = some a) :
    picking_prefix_state seq rank (k + 1) =
      picking_turn (List.ofFn ⇑(rank a)) a (picking_prefix_state seq rank k) := by
  dsimp [picking_prefix_state]
  rw [List.take_add_one, hk]
  simp

theorem round_robin_divergence_turn_actor_turn_snd_eq {N G : Type*} [DecidableEq N] [DecidableEq G]
    (a : N) (l : List G) (st st' : (N → Finset G) × Finset G)
    (hst : st.2 = st'.2) :
    (picking_turn l a st).2 = (picking_turn l a st').2 := by
  unfold picking_turn
  have hpred : (fun g => decide (g ∉ st.2)) = (fun g => decide (g ∉ st'.2)) := by
    rw [hst]
  rw [hpred]
  split
  · simp [hst]
  · exact hst

/-- When only agent i changes their bid, the earliest turn t < m where the allocated item set diverges between the two runs must be a turn where agent i acts. -/
theorem round_robin_divergence_turn_actor (n m : ℕ) [NeZero n]
    (b b' : Fin n → Fin m ≃ Fin m) (i : Fin n)
    (hupd : b' = Function.update b i (b' i))
    (t : ℕ) (ht : t < m)
    (heq : ∀ s ≤ t, (picking_prefix_state (round_robin_sequence n m) b s).2 =
                    (picking_prefix_state (round_robin_sequence n m) b' s).2)
    (hne : (picking_prefix_state (round_robin_sequence n m) b (t + 1)).2 ≠
           (picking_prefix_state (round_robin_sequence n m) b' (t + 1)).2) :
    (round_robin_sequence n m)[t]? = some i := by
  have hlen : (round_robin_sequence n m).length = m := by
    simp [round_robin_sequence]
  have ht' : t < (round_robin_sequence n m).length := by omega
  set a := (round_robin_sequence n m)[t]
  have ha : (round_robin_sequence n m)[t]? = some a := List.getElem?_eq_getElem ht'
  have heqi : a = i := by
    by_contra hne_ai
    have hba : b' a = b a := by
      rw [hupd]
      exact Function.update_of_ne hne_ai (b' i) b
    have h1 : picking_prefix_state (round_robin_sequence n m) b (t + 1) =
        picking_turn (List.ofFn ⇑(b a)) a (picking_prefix_state (round_robin_sequence n m) b t) :=
      round_robin_divergence_turn_actor_prefix_succ (round_robin_sequence n m) b t a ha
    have h2 : picking_prefix_state (round_robin_sequence n m) b' (t + 1) =
        picking_turn (List.ofFn ⇑(b' a)) a (picking_prefix_state (round_robin_sequence n m) b' t) :=
      round_robin_divergence_turn_actor_prefix_succ (round_robin_sequence n m) b' t a ha
    have hst : (picking_prefix_state (round_robin_sequence n m) b t).2 =
        (picking_prefix_state (round_robin_sequence n m) b' t).2 :=
      heq t le_rfl
    have hturn : (picking_turn (List.ofFn ⇑(b a)) a (picking_prefix_state (round_robin_sequence n m) b t)).2 =
        (picking_turn (List.ofFn ⇑(b' a)) a (picking_prefix_state (round_robin_sequence n m) b' t)).2 := by
      rw [hba]
      exact round_robin_divergence_turn_actor_turn_snd_eq a (List.ofFn ⇑(b a))
        (picking_prefix_state (round_robin_sequence n m) b t)
        (picking_prefix_state (round_robin_sequence n m) b' t) hst
    apply hne
    rw [h1, h2, hturn]
  rw [heqi] at ha
  exact ha
