import AFTD.Prelude
import AFTD.Kb.Tcs.CarpoolStep

/-!
# op_2130_carpool_fold_avoids_vertex

Topic: online_algorithms   Node: 23e053ed1d1b

Provenance: helper lemma. Independent-path-block construction for refuting op_2130_path_greedy_fixed_time_tail

A sequence of carpool updates whose requested edges all avoid a vertex leaves that vertex’s discrepancy unchanged.
-/

theorem op_2130_carpool_fold_avoids_vertex (n : ℕ) (edges : List (Fin n × Fin n)) (signs : List Bool) (d : Fin n → ℤ) (v : Fin n) (h : ∀ e ∈ edges, v ≠ e.1 ∧ v ≠ e.2) : ((edges.zip signs).foldl (fun d (e, b) => carpool_step n d e b) d) v = d v := by
  induction edges generalizing signs d with
  | nil => simp
  | cons e es ih =>
    cases signs with
    | nil => simp
    | cons b bs =>
      have he := h e (List.mem_cons_self ..)
      have ht : ∀ e ∈ es, v ≠ e.1 ∧ v ≠ e.2 := fun e he => h e (List.mem_cons_of_mem _ he)
      simp only [List.zip_cons_cons, List.foldl_cons]
      rw [ih bs (carpool_step n d e b) ht]
      simp [carpool_step, he.1, he.2]
