import AFTD.Prelude
import AFTD.Kb.Tcs.CompleteColoringClassicalValue

/-!
# complete_coloring_synchronous_optimal

Topic: quantum   Node: 0480b572cbb6

Provenance: formalization of a published result. Source: arXiv:2611.19002, Quantum Coloring Games on Complete Graphs, Section 2.1 and 3.3

A synchronous classical strategy is optimal for the complete-graph coloring game at probability p if there exists a synchronous strategy achieving value at least that of every classical strategy.
-/

/-- Predicate asserting that a synchronous classical strategy achieves optimal value across all classical strategies. -/
def complete_coloring_synchronous_optimal (n m : ℕ) (p : ℝ) : Prop :=
  ∃ s : Fin n → Fin m, ∀ a b : Fin n → Fin m,
    complete_coloring_classical_value n m p a b ≤ complete_coloring_classical_value n m p s s
