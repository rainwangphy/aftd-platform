import AFTD.Prelude
import AFTD.Kb.Tcs.IsParityRepr
import AFTD.Kb.Tcs.CczLayerSyndrome

/-!
# ccz_layer_parity_repr_two

Topic: quantum   Node: 2eb65cd0091e

Two disjoint CCZ gates have a parity representation with 13 = 6 * 2 + 1 parities, so the Hadamard-free T-count of the layer with m = 2 is at most 13.
-/

theorem ccz_layer_parity_repr_two : ∃ S : Finset (Finset (Fin 6)), is_parity_repr S (ccz_layer_syndrome 2) ∧ S.card = 13 := by
  refine ⟨{{0, 1, 2, 3, 4, 5}, {0, 1, 2, 3, 4}, {0, 1, 2, 3, 5}, {0, 1, 2, 3}, {0, 1, 2, 4, 5}, {0, 1, 2, 4}, {0, 1, 2, 5}, {0, 1}, {0, 2}, {0}, {1, 2}, {1}, {2}}, ?_, by decide +kernel⟩
  unfold is_parity_repr
  decide +kernel
