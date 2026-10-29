import AFTD.Prelude
import AFTD.Kb.Tcs.CyclicCubicSyndrome
import AFTD.Kb.Tcs.IsParityRepr

/-!
# cyclic_cubic_t_count_six

Topic: quantum   Node: fd8ff874f2ad

Provenance: original. Related work: arXiv:2610.01024

There exists a finite set S : Finset (Finset (Fin 6)) such that is_parity_repr S (cyclic_cubic_syndrome 6) and S.card = 17.
-/

/-- For n = 6, there exists a parity representation of the cyclic cubic syndrome of cardinality 17. -/
theorem cyclic_cubic_t_count_six : ∃ S : Finset (Finset (Fin 6)), is_parity_repr S (cyclic_cubic_syndrome 6) ∧ S.card = 17 := by
  refine ⟨{{0, 1}, {0, 1, 2}, {0, 3}, {0, 1, 3}, {0, 1, 2, 3}, {2, 4}, {1, 3, 4}, {0, 1, 3, 4},
    {2, 3, 4}, {5}, {0, 3, 5}, {0, 4, 5}, {2, 4, 5}, {0, 2, 4, 5}, {3, 4, 5},
    {1, 2, 3, 4, 5}, {0, 1, 2, 3, 4, 5}}, ?_, by decide +kernel⟩
  unfold is_parity_repr cyclic_cubic_syndrome
  decide +kernel
