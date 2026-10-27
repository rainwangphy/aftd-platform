import AFTD.Prelude
import AFTD.Kb.Tcs.TournamentIsNearRegular
import AFTD.Kb.Tcs.DigraphIsTournament
import AFTD.Kb.Tcs.DigraphArborescenceCount

/-!
# tournament_four_arborescence_maximizer_is_near_regular

Topic: graphs   Node: af28ee20cb65

Provenance: original. Related work: arXiv:2610.25886

Every tournament on 4 vertices maximizing the total number of spanning arborescences among all tournaments on 4 vertices is near-regular.
-/

private def tournament_four_bit_of_fn (b : Fin 6 → Bool) (i j : Fin 4) : Bool :=
  match i, j with
  | 0, 1 => b 0
  | 0, 2 => b 1
  | 0, 3 => b 2
  | 1, 2 => b 3
  | 1, 3 => b 4
  | 2, 3 => b 5
  | 1, 0 => !b 0
  | 2, 0 => !b 1
  | 3, 0 => !b 2
  | 2, 1 => !b 3
  | 3, 1 => !b 4
  | 3, 2 => !b 5
  | _, _ => false

private def tournament_four_T_of_bools (b : Fin 6 → Bool) : Digraph (Fin 4) where
  Adj i j := tournament_four_bit_of_fn b i j = true

private instance (b : Fin 6 → Bool) : DecidableRel (tournament_four_T_of_bools b).Adj := by
  intro i j
  dsimp [tournament_four_T_of_bools]
  infer_instance

private instance tournament_four_dec_tourn (V : Type*) [Fintype V] [DecidableEq V] (D : Digraph V) [DecidableRel D.Adj] :
    Decidable (digraph_is_tournament D) := by
  dsimp [digraph_is_tournament]
  infer_instance

private instance tournament_four_dec_nr (m : ℕ) (D : Digraph (Fin (2 * m))) [DecidableRel D.Adj] :
    Decidable (tournament_is_near_regular m D) := by
  dsimp [tournament_is_near_regular]
  infer_instance

private theorem tournament_four_check_bools :
    ∀ b : Fin 6 → Bool, ¬ tournament_is_near_regular 2 (tournament_four_T_of_bools b) →
      digraph_arborescence_count (tournament_four_T_of_bools b) ≤ 9 := by
  decide

private def tournament_four_b_max : Fin 6 → Bool
  | 0 => true
  | 1 => true
  | 2 => false
  | 3 => true
  | 4 => true
  | 5 => true

private theorem tournament_four_b_max_tourn : digraph_is_tournament (tournament_four_T_of_bools tournament_four_b_max) := by decide
private theorem tournament_four_b_max_count : digraph_arborescence_count (tournament_four_T_of_bools tournament_four_b_max) = 10 := by decide

private def tournament_four_bools_of_T (T : Digraph (Fin 4)) [DecidableRel T.Adj] : Fin 6 → Bool
  | 0 => decide (T.Adj 0 1)
  | 1 => decide (T.Adj 0 2)
  | 2 => decide (T.Adj 0 3)
  | 3 => decide (T.Adj 1 2)
  | 4 => decide (T.Adj 1 3)
  | 5 => decide (T.Adj 2 3)

private theorem tournament_four_T_eq_T_of_bools (T : Digraph (Fin 4)) [DecidableRel T.Adj] (hT : digraph_is_tournament T) :
    T = tournament_four_T_of_bools (tournament_four_bools_of_T T) := by
  cases T with | mk Adj =>
  dsimp [tournament_four_T_of_bools]
  congr
  funext ⟨i, hi⟩ ⟨j, hj⟩
  apply propext
  obtain ⟨h_loop, h_tourn⟩ := hT
  dsimp at h_loop h_tourn
  interval_cases i <;> interval_cases j
  · change Adj 0 0 ↔ tournament_four_bit_of_fn (tournament_four_bools_of_T { Adj := Adj }) 0 0 = true
    dsimp [tournament_four_bit_of_fn]; simp [h_loop 0]
  · change Adj 0 1 ↔ tournament_four_bit_of_fn (tournament_four_bools_of_T { Adj := Adj }) 0 1 = true
    dsimp [tournament_four_bit_of_fn, tournament_four_bools_of_T]; simp
  · change Adj 0 2 ↔ tournament_four_bit_of_fn (tournament_four_bools_of_T { Adj := Adj }) 0 2 = true
    dsimp [tournament_four_bit_of_fn, tournament_four_bools_of_T]; simp
  · change Adj 0 3 ↔ tournament_four_bit_of_fn (tournament_four_bools_of_T { Adj := Adj }) 0 3 = true
    dsimp [tournament_four_bit_of_fn, tournament_four_bools_of_T]; simp
  · change Adj 1 0 ↔ tournament_four_bit_of_fn (tournament_four_bools_of_T { Adj := Adj }) 1 0 = true
    rw [h_tourn 1 0 (by decide)]; dsimp [tournament_four_bit_of_fn, tournament_four_bools_of_T]; simp
  · change Adj 1 1 ↔ tournament_four_bit_of_fn (tournament_four_bools_of_T { Adj := Adj }) 1 1 = true
    dsimp [tournament_four_bit_of_fn]; simp [h_loop 1]
  · change Adj 1 2 ↔ tournament_four_bit_of_fn (tournament_four_bools_of_T { Adj := Adj }) 1 2 = true
    dsimp [tournament_four_bit_of_fn, tournament_four_bools_of_T]; simp
  · change Adj 1 3 ↔ tournament_four_bit_of_fn (tournament_four_bools_of_T { Adj := Adj }) 1 3 = true
    dsimp [tournament_four_bit_of_fn, tournament_four_bools_of_T]; simp
  · change Adj 2 0 ↔ tournament_four_bit_of_fn (tournament_four_bools_of_T { Adj := Adj }) 2 0 = true
    rw [h_tourn 2 0 (by decide)]; dsimp [tournament_four_bit_of_fn, tournament_four_bools_of_T]; simp
  · change Adj 2 1 ↔ tournament_four_bit_of_fn (tournament_four_bools_of_T { Adj := Adj }) 2 1 = true
    rw [h_tourn 2 1 (by decide)]; dsimp [tournament_four_bit_of_fn, tournament_four_bools_of_T]; simp
  · change Adj 2 2 ↔ tournament_four_bit_of_fn (tournament_four_bools_of_T { Adj := Adj }) 2 2 = true
    dsimp [tournament_four_bit_of_fn]; simp [h_loop 2]
  · change Adj 2 3 ↔ tournament_four_bit_of_fn (tournament_four_bools_of_T { Adj := Adj }) 2 3 = true
    dsimp [tournament_four_bit_of_fn, tournament_four_bools_of_T]; simp
  · change Adj 3 0 ↔ tournament_four_bit_of_fn (tournament_four_bools_of_T { Adj := Adj }) 3 0 = true
    rw [h_tourn 3 0 (by decide)]; dsimp [tournament_four_bit_of_fn, tournament_four_bools_of_T]; simp
  · change Adj 3 1 ↔ tournament_four_bit_of_fn (tournament_four_bools_of_T { Adj := Adj }) 3 1 = true
    rw [h_tourn 3 1 (by decide)]; dsimp [tournament_four_bit_of_fn, tournament_four_bools_of_T]; simp
  · change Adj 3 2 ↔ tournament_four_bit_of_fn (tournament_four_bools_of_T { Adj := Adj }) 3 2 = true
    rw [h_tourn 3 2 (by decide)]; dsimp [tournament_four_bit_of_fn, tournament_four_bools_of_T]; simp
  · change Adj 3 3 ↔ tournament_four_bit_of_fn (tournament_four_bools_of_T { Adj := Adj }) 3 3 = true
    dsimp [tournament_four_bit_of_fn]; simp [h_loop 3]

/-- Total arborescence maximizers on 4 vertices are near-regular (m = 2 base case of OP-545). -/
theorem tournament_four_arborescence_maximizer_is_near_regular
    (T : Digraph (Fin 4)) [DecidableRel T.Adj] (hT : digraph_is_tournament T)
    (hmax : ∀ (T' : Digraph (Fin 4)) [DecidableRel T'.Adj],
      digraph_is_tournament T' → digraph_arborescence_count T' ≤ digraph_arborescence_count T) :
    tournament_is_near_regular 2 T := by
  have h10 : 10 ≤ digraph_arborescence_count T := by
    have hle := hmax (tournament_four_T_of_bools tournament_four_b_max) tournament_four_b_max_tourn
    rw [tournament_four_b_max_count] at hle
    exact hle
  have hT_eq := tournament_four_T_eq_T_of_bools T hT
  by_contra hnr
  generalize hb : tournament_four_bools_of_T T = b at hT_eq ⊢
  have hnr' : ¬ tournament_is_near_regular 2 (tournament_four_T_of_bools b) := by
    intro h
    apply hnr
    have h_eq : tournament_is_near_regular 2 T ↔ tournament_is_near_regular 2 (tournament_four_T_of_bools b) := by
      subst hT_eq
      congr!
    rwa [h_eq]
  have hle9 := tournament_four_check_bools b hnr'
  have h_count_eq : digraph_arborescence_count T = digraph_arborescence_count (tournament_four_T_of_bools b) := by
    subst hT_eq
    congr
  omega
