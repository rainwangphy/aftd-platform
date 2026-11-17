import AFTD.Prelude

/-!
# prioritized_borel_padding_offset_nonzero_frequently

Topic: automata   Node: a0b823cb7236

Provenance: helper lemma. Priority padding for the state-history reduction of arXiv:2611.10136, Conjecture 19.

When each original priority is placed at the fixed offset r inside a length L block and all other positions contain zero, any nonzero priority occurs infinitely often exactly when it did before padding, provided r is less than L.
-/

theorem prioritized_borel_padding_offset_nonzero_frequently (L r : ℕ) (hr : r < L) (f : ℕ → Fin 3) (p : Fin 3) (hp : p ≠ 0) : (Filter.Frequently (fun n => (if n % L = r then f (n / L) else 0) = p) Filter.atTop) ↔ Filter.Frequently (fun n => f n = p) Filter.atTop := by
  have hL : 0 < L := by omega
  rw [Filter.frequently_atTop, Filter.frequently_atTop]
  constructor
  · intro h N
    obtain ⟨m, hm, hmval⟩ := h (N * L)
    split_ifs at hmval with hz
    · have hdiv : N ≤ m / L := (Nat.le_div_iff_mul_le hL).2 hm
      exact ⟨m / L, hdiv, hmval⟩
    · exact False.elim (hp hmval.symm)
  · intro h N
    obtain ⟨m, hm, hmval⟩ := h N
    refine ⟨r + m * L, ?_, ?_⟩
    · exact le_trans hm (le_trans (Nat.le_mul_of_pos_right _ hL) (Nat.le_add_left _ _))
    · simpa [Nat.mod_eq_of_lt hr, Nat.div_eq_of_lt hr, Nat.add_mul_div_right _ _ hL] using hmval
