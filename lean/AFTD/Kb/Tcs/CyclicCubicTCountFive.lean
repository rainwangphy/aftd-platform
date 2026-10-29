import AFTD.Prelude
import AFTD.Kb.Tcs.CyclicCubicSyndrome
import AFTD.Kb.Tcs.IsParityRepr

/-!
# cyclic_cubic_t_count_five

Topic: quantum   Node: 5b0b3f15faf4

Provenance: original. Related work: arXiv:2610.01024

There exists a finite set S : Finset (Finset (Fin 5)) such that is_parity_repr S (cyclic_cubic_syndrome 5) and S.card = 11.
-/

/-- For n = 5, there exists a parity representation of the cyclic cubic syndrome of cardinality 11. -/
theorem cyclic_cubic_t_count_five : ∃ S : Finset (Finset (Fin 5)), is_parity_repr S (cyclic_cubic_syndrome 5) ∧ S.card = 11 := by
  refine ⟨{{1}, {0, 1}, {2}, {0, 3}, {2, 3}, {0, 1, 4}, {1, 2, 4}, {0, 1, 3, 4}, {2, 3, 4}, {0, 2, 3, 4}, {0, 1, 2, 3, 4}}, ?_, by decide +kernel⟩
  unfold is_parity_repr cyclic_cubic_syndrome
  decide +kernel
