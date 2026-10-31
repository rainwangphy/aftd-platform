import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphReverseArc
import AFTD.Kb.Tcs.DigraphReverseArcAdj
import AFTD.Kb.Tcs.DigraphIsTournament

/-!
# tournament_reverse_arc_is_tournament

Topic: graphs   Node: 5d18e2b161cc

Provenance: helper lemma. step towards tournament_not_near_regular_exists_improving_tournament

If T is a tournament with an arc u → v, reversing that arc gives another tournament.
-/

/-- Reversing the arc u → v of a tournament again yields a tournament. -/
theorem tournament_reverse_arc_is_tournament {n : ℕ} (T : Digraph (Fin n)) [DecidableRel T.Adj]
    (hT : digraph_is_tournament T) (u v : Fin n) (huv : T.Adj u v) :
    digraph_is_tournament (digraph_reverse_arc T u v) := by
  have unev : u ≠ v := by
    rintro rfl
    exact hT.1 u huv
  constructor
  · intro x
    dsimp [digraph_reverse_arc]
    split_ifs with h
    · cases h with
      | inl h1 => exact (unev (h1.1.symm.trans h1.2)).elim
      | inr h2 => exact (unev (h2.2.symm.trans h2.1)).elim
    · exact hT.1 x
  · intro x y hne
    dsimp [digraph_reverse_arc]
    have hiff : ((x = u ∧ y = v) ∨ (x = v ∧ y = u)) ↔ ((y = u ∧ x = v) ∨ (y = v ∧ x = u)) := by
      tauto
    by_cases h : (x = u ∧ y = v) ∨ (x = v ∧ y = u)
    · have h' : (y = u ∧ x = v) ∨ (y = v ∧ x = u) := hiff.mp h
      rw [if_pos h, if_pos h']
      exact hT.2 y x hne.symm
    · have h' : ¬ ((y = u ∧ x = v) ∨ (y = v ∧ x = u)) := by rwa [← hiff]
      rw [if_neg h, if_neg h']
      exact hT.2 x y hne
