import AFTD.Prelude

/-!
# xz_cyclic_succ

Topic: quantum_mechanics   Node: ac620d6f63b0

Provenance: helper lemma. step towards xz_scar_uniform_reduced_spectrum_odd_length_doubling

The cyclic successor `i ↦ (i + 1) mod n` on `Fin n`, total also for `n = 0` (where the argument is impossible).
-/

/-- The cyclic successor `(i + 1) mod n` on `Fin n`. -/
def xz_cyclic_succ {n : ℕ} (i : Fin n) : Fin n := ⟨(i.val + 1) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)⟩
