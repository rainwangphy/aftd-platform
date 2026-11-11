import AFTD.Prelude

/-!
# dephased_path_interval_block

Topic: quantum_mechanics   Node: f703a65de4f9

Provenance: helper lemma. Alternating supported-kernel block for the OP-827 path reduction.

The positions of the same parity as the left endpoint in a finite path interval.
-/

def dephased_path_interval_block (n : ℕ) (i j : Fin n) : Finset (Fin n) := Finset.univ.filter fun k => i.val ≤ k.val ∧ k.val ≤ j.val ∧ k.val % 2 = i.val % 2
