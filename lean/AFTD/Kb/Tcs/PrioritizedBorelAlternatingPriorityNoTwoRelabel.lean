import AFTD.Prelude

/-!
# prioritized_borel_alternating_priority_no_two_relabel

Topic: automata   Node: ad3130702704

Provenance: helper lemma. Structural step related to arXiv:2611.10136, Conjecture 19.

The alternating acceptance pattern false, true, false on three priorities cannot be represented for all recurrent-priority sets by any fixed relabelling into two priorities and any two acceptance values.
-/

theorem prioritized_borel_alternating_priority_no_two_relabel :
    ¬ ∃ (f : Fin 3 → Fin 2) (w : Fin 2 → Bool),
      w (f 0) = false ∧ w (f 1) = true ∧ w (f 2) = false ∧
      w (max (f 0) (f 1)) = true ∧ w (max (f 1) (f 2)) = false := by
  decide +kernel
