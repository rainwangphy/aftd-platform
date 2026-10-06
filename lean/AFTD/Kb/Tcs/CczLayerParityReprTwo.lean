import AFTD.Prelude
import AFTD.Kb.Tcs.IsParityRepr
import AFTD.Kb.Tcs.CczLayerSyndrome

/-!
# ccz_layer_parity_repr_two

Topic: quantum   Node: 2eb65cd0091e

Provenance: formalization of a published result. Source: Exact T-counts of Toffoli Layers from an Isotropy Bound, arXiv:2610.01024, Theorem 40 (upper bound via Proposition 47 / Lemma 46: a parity representation of weight 6m + 1); special case m = 2, the value 13 also reported earlier by the synthillation construction cited there

Two disjoint CCZ gates have a parity representation with 13 = 6 * 2 + 1 parities, so the Hadamard-free T-count of the layer with m = 2 is at most 13.
-/

theorem ccz_layer_parity_repr_two : ∃ S : Finset (Finset (Fin 6)), is_parity_repr S (ccz_layer_syndrome 2) ∧ S.card = 13 := by
  refine ⟨{{0, 1, 2, 3, 4, 5}, {0, 1, 2, 3, 4}, {0, 1, 2, 3, 5}, {0, 1, 2, 3}, {0, 1, 2, 4, 5}, {0, 1, 2, 4}, {0, 1, 2, 5}, {0, 1}, {0, 2}, {0}, {1, 2}, {1}, {2}}, ?_, by decide +kernel⟩
  unfold is_parity_repr
  decide +kernel
