import AFTD.Prelude

/-!
# dephased_path_binary_weight

Topic: quantum_mechanics   Node: c889dd0316e3

Provenance: helper lemma. Constant-gap certificate for the OP-827 path reduction.

The zero-one weight of natural position k in the path support P.
-/

noncomputable def dephased_path_binary_weight (n : ℕ) (P : Finset (Fin n)) (k : ℕ) : ℝ := open scoped Classical in if ∃ i ∈ P, i.val = k then 1 else 0
