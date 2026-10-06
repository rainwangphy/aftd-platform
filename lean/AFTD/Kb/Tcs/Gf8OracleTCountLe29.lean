import AFTD.Prelude
import AFTD.Kb.Tcs.IsParityRepr
import AFTD.Kb.Tcs.Gf8OracleSyndrome

/-!
# gf8_oracle_t_count_le_29

Topic: quantum   Node: 2f59a68020ca

Provenance: formalization of a published result. Source: Exact T-counts of Toffoli Layers from an Isotropy Bound, arXiv:2610.01024, Open Problem 10: the best published circuit for the GF(8) oracle already has T-count 23, so this bound 29 is weaker than the published one; the 29-parity certificate itself was found here by SAT search

The GF(8) multiplication oracle has a parity representation with 29 parities, so its T-count delta(U_3) in Hadamard-free {CNOT, T} circuits is at most 29 (an explicit certificate found by SAT search; the merged schoolbook expansion has 36).
-/

theorem gf8_oracle_t_count_le_29 : ∃ S : Finset (Finset (Fin 9)), is_parity_repr S gf8_oracle_syndrome ∧ S.card = 29 := by
  refine ⟨{{0, 1, 2, 3, 5, 6, 7}, {0, 1, 2, 3, 5, 7}, {0, 1, 2, 4, 6, 7}, {0, 1, 2, 4, 8}, {0, 1, 2, 7}, {0, 1, 2, 8}, {0, 2, 4, 5, 6, 7, 8}, {0, 2, 4, 5, 7}, {0, 2, 6, 7, 8}, {0, 2, 7}, {1, 2, 3, 5, 6, 7, 8}, {1, 2, 3, 5, 8}, {1, 2, 4, 5, 6, 8}, {1, 2, 4, 5, 7, 8}, {1, 3, 5, 6, 7, 8}, {1, 3, 5, 6, 8}, {1, 3, 7, 8}, {1, 3, 8}, {2, 3, 4, 5, 7, 8}, {2, 3, 4, 5, 7}, {2, 3, 6, 7}, {2, 3, 6}, {2, 4, 5, 7, 8}, {2, 4, 5}, {3, 4, 5, 6, 8}, {3, 4, 5, 6}, {4, 6, 8}, {4, 7}, {6, 7}}, ?_, by decide +kernel⟩
  unfold is_parity_repr
  decide +kernel
