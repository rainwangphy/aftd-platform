import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.PickingSequenceOutcome
import AFTD.Kb.GameTheoryEconomics.PickingTurn

/-!
# independent_rank_trajectories_single_good

Topic: fair_division   Node: b2caeb2273a8

Provenance: original. Related work: OP-1532

For n ≥ 2 agents and m = 1 good, under any length-1 picking sequence, the agents' received rank vectors are mutually independent under uniformly random rankings.
-/

/-- With one good, a length-one picking sequence gives the good only to its sole scheduled agent. -/
private lemma independent_rank_trajectories_single_good_trajectory (n : ℕ) (a i : Fin n)
    (r : Fin n → Fin 1 ≃ Fin 1) :
    ((picking_sequence_outcome [a] r i).image (r i).symm).sort (· ≤ ·) =
      (if i = a then [0] else []) := by
  by_cases h : i = a
  · subst h
    simp [picking_sequence_outcome, picking_turn]
  · simp [picking_sequence_outcome, picking_turn, h]

/-- Normalizing the cardinality of a filter over a singleton type gives the indicator of its predicate. -/
private lemma independent_rank_trajectories_single_good_card_filter_unique_div
    (α : Type*) [Fintype α] [Unique α] (P : α → Prop) [DecidablePred P] :
    (((Finset.univ : Finset α).filter P).card : ℚ) / (Fintype.card α : ℚ) =
      if P default then 1 else 0 := by
  rw [Finset.univ_unique, Finset.filter_singleton]
  by_cases h : P default
  · simp [h, Fintype.card_unique]
  · simp [h, Fintype.card_unique]

/-- For any number of agents n ≥ 2 and m = 1 good, the agents' received rank vectors are mutually independent under a length-1 picking sequence. -/
theorem independent_rank_trajectories_single_good (n : ℕ) (hn : 2 ≤ n)
    (seq : List (Fin n)) (hlen : seq.length = 1) (s : Fin n → List (Fin 1)) :
    (((Finset.univ : Finset (Fin n → Fin 1 ≃ Fin 1)).filter
      (fun r => ∀ i, ((picking_sequence_outcome seq r i).image (r i).symm).sort (· ≤ ·) = s i)).card : ℚ) /
    (Fintype.card (Fin n → Fin 1 ≃ Fin 1) : ℚ) =
    ∏ i : Fin n,
      (((Finset.univ : Finset (Fin n → Fin 1 ≃ Fin 1)).filter
        (fun r => ((picking_sequence_outcome seq r i).image (r i).symm).sort (· ≤ ·) = s i)).card : ℚ) /
      (Fintype.card (Fin n → Fin 1 ≃ Fin 1) : ℚ) := by
  obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hlen
  simp only [independent_rank_trajectories_single_good_trajectory]
  simp only [independent_rank_trajectories_single_good_card_filter_unique_div]
  rw [Finset.prod_boole]
  simp
