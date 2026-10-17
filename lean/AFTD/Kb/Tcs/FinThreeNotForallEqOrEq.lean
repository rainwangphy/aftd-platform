import AFTD.Prelude

/-!
# fin_three_not_forall_eq_or_eq

Topic: combinatorics   Node: c88671d77a0d

Provenance: helper lemma. Helper for simple_graph_cycle_power_three_cover_three_tight_dvd (thread RT-1, the k = 3 case of OP-205, arXiv:2610.15635).

Two elements of Fin 3 never exhaust it.
-/

theorem fin_three_not_forall_eq_or_eq : ∀ x y : Fin 3, ¬ ∀ s : Fin 3, s = x ∨ s = y := by
  intro x y; fin_cases x <;> fin_cases y <;> decide
