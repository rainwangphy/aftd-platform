import AFTD.Prelude

/-!
# fin_three_eq_of_five_ne

Topic: combinatorics   Node: f69703a431b2

Provenance: helper lemma. Helper for simple_graph_cycle_power_three_cover_three_tight_dvd (thread RT-1, the k = 3 case of OP-205, arXiv:2610.15635).

In Fin 3, if a, c, d are distinct, b ∉ {c, e}, c ≠ e and a ≠ b, then e = a.
-/

theorem fin_three_eq_of_five_ne : ∀ a b c d e : Fin 3, a ≠ c → a ≠ d → c ≠ d → b ≠ c → b ≠ e →
    c ≠ e → a ≠ b → e = a := by
  intro a b c d e
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> fin_cases e <;> simp
