import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CyclicOffset

/-!
# cyclic_offset_eq_ite

Topic: matching_markets   Node: 59a893ead821

For i, j in {0, ..., n-1}, the cyclic offset (j - i) mod n equals j - i when i <= j and j + n - i otherwise.
-/

theorem cyclic_offset_eq_ite {n : ℕ} (i j : Fin n) :
    cyclic_offset i j = if (i : ℕ) ≤ j then (j : ℕ) - i else (j : ℕ) + n - i := by
  unfold cyclic_offset
  have hi := i.isLt
  have hj := j.isLt
  split_ifs with h
  · have e : (j : ℕ) + n - i = ((j : ℕ) - i) + n := by omega
    rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)
