import AFTD.Prelude

/-!
# prioritized_borel_padding_nonzero_frequently

Topic: automata   Node: cdff151d5551

Provenance: helper lemma. Padding step for the state-history encoding route for arXiv:2611.10136, Conjecture 19.

Inserting L minus one occurrences of the lowest priority between successive priorities preserves which nonzero priorities occur infinitely often, for every positive block length L.
-/

theorem prioritized_borel_padding_nonzero_frequently (L : ℕ) (hL : 0 < L) (f : ℕ → Fin 3) (p : Fin 3) (hp : p ≠ 0) : (Filter.Frequently (fun n => (if n % L = 0 then f (n / L) else 0) = p) Filter.atTop) ↔ Filter.Frequently (fun n => f n = p) Filter.atTop := by
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
    refine ⟨m * L, ?_, ?_⟩
    · exact le_trans hm (Nat.le_mul_of_pos_right _ hL)
    · simpa [Nat.mul_mod_right, Nat.mul_div_cancel _ hL] using hmval
