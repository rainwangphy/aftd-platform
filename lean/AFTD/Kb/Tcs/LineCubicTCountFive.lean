import AFTD.Prelude
import AFTD.Kb.Tcs.LineSyndrome
import AFTD.Kb.Tcs.IsParityRepr

/-!
# line_cubic_t_count_five

Topic: quantum   Node: 1363e47bd07a

For n = 5, there exists a parity representation of the line cubic syndrome of cardinality 11.
-/

/-- Tightness at n = 5: the line cubic syndrome admits a parity representation of size 11. -/
theorem line_cubic_t_count_five : ∃ S : Finset (Finset (Fin 5)), is_parity_repr S (line_syndrome 5) ∧ S.card = 11 := by
  refine ⟨{{0, 3, 4}, {0, 1, 3, 4}, {1, 4}, {1, 2, 4}, {0, 2, 3, 4}, {0, 1, 2, 3, 4}, {2, 3, 4}, {2}, {2, 3}, {3}, {3, 4}}, ?_, by decide +kernel⟩
  unfold is_parity_repr line_syndrome
  decide +kernel
