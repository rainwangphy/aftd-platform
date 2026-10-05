import AFTD.Prelude
import AFTD.Kb.Tcs.LineSyndrome
import AFTD.Kb.Tcs.IsParityRepr

/-!
# line_cubic_t_count_six

Topic: quantum   Node: 420ea70ecd3a

For n = 6, there exists a parity representation of the line cubic syndrome of cardinality 13.
-/

/-- Tightness at n = 6: the line cubic syndrome admits a parity representation of size 13. -/
theorem line_cubic_t_count_six : ∃ S : Finset (Finset (Fin 6)), is_parity_repr S (line_syndrome 6) ∧ S.card = 13 := by
  refine ⟨{{0, 1, 2, 3, 4, 5}, {0, 1, 3, 4, 5}, {0, 2, 3, 4, 5}, {0, 3, 4, 5}, {1, 2, 4, 5}, {1, 4, 5}, {2, 3, 4, 5}, {2, 3, 5}, {2, 5}, {3}, {3, 4}, {4}, {4, 5}}, ?_, by decide +kernel⟩
  unfold is_parity_repr line_syndrome
  decide +kernel
