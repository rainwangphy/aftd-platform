import AFTD.Prelude
import AFTD.Kb.Tcs.CarpoolStep
import AFTD.Kb.Tcs.CarpoolGreedyOrientations

/-!
# op_2130_right_moves_are_greedy

Topic: online_algorithms   Node: 8c3207190a4e

Provenance: helper lemma. OP-2130: identify a deterministic legal right-moving trajectory with randomized greedy on an all-false coin tape

If the first endpoint has at least the discrepancy of the second endpoint before every move in the all-false trajectory, greedy with all-false coins chooses false at every request.
-/

private lemma op2130_aux_false_greedy (n : ℕ) (es : List (Fin n × Fin n)) (d : Fin n → ℤ)
    (h : ∀ k (hk : k < es.length),
      let s := (es.take k).foldl (fun d e => carpool_step n d e false) d
      s (es[k]).2 ≤ s (es[k]).1) :
    carpool_greedy_orientations.aux n es (List.replicate es.length false) d = List.replicate es.length false := by
  induction es generalizing d with
  | nil => simp [carpool_greedy_orientations.aux]
  | cons e es ih =>
    have h0 : d e.2 ≤ d e.1 := by
      have hh := h 0 (by simp)
      dsimp at hh
      exact hh
    have htail : ∀ k (hk : k < es.length),
      let s := (es.take k).foldl (fun d e => carpool_step n d e false) (carpool_step n d e false)
      s (es[k]).2 ≤ s (es[k]).1 := by
      intro k hk
      have hh := h (k + 1) (by simp; omega)
      simpa [List.take_succ_cons] using hh
    simp only [List.length_cons, List.replicate_succ, carpool_greedy_orientations.aux]
    simp [not_lt.mpr h0, ih _ htail]

theorem op_2130_right_moves_are_greedy (n : ℕ) (edges : List (Fin n × Fin n)) (h : ∀ k (hk : k < edges.length), let d := (edges.take k).foldl (fun d e => carpool_step n d e false) (fun _ => 0); d (edges[k]).2 ≤ d (edges[k]).1) : carpool_greedy_orientations n edges (List.replicate edges.length false) = List.replicate edges.length false := by
  unfold carpool_greedy_orientations
  exact op2130_aux_false_greedy n edges (fun _ => 0) h
