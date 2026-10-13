import AFTD.Prelude
import AFTD.Kb.Tcs.LowerOnesMatrix
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# lower_ones_matrix_apply_self

Topic: graphs   Node: 6f4a9a14d38b

Provenance: helper lemma. Sanity lemma for lower_ones_matrix (arXiv:2610.13798).

The diagonal entries of L are 1.
-/

theorem lower_ones_matrix_apply_self (n : ℕ) (i : Fin n) : lower_ones_matrix n i i = 1 := by
  simp [lower_ones_matrix]
