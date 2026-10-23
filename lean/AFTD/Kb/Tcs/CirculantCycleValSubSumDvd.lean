import AFTD.Prelude

/-!
# circulant_cycle_val_sub_sum_dvd

Topic: graphs   Node: 28bff38f40e5

Provenance: helper lemma. step towards circulant_mixed_graph_no_cycle_lt_g

The sum of cyclic differences of any function x : Fin t → Fin N is a multiple of N.
-/

/-- The sum of cyclic differences of any function x : Fin t → Fin N is a multiple of N. -/
theorem circulant_cycle_val_sub_sum_dvd {t N : ℕ} (x : Fin t → Fin N) :
    N ∣ ∑ i : Fin t, (x (finRotate t i) - x i).val := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  have h (i : Fin t) : (((x (finRotate t i) - x i).val : ZMod N) : ZMod N) =
      (x (finRotate t i)).val - (x i).val := by
    rw [Fin.val_sub, ZMod.natCast_mod]
    push_cast
    rw [Nat.cast_sub (le_of_lt (x i).isLt), ZMod.natCast_self, zero_sub]
    ring
  simp_rw [h]
  rw [Finset.sum_sub_distrib, Equiv.sum_comp (finRotate t) (fun i => ((x i).val : ZMod N)), sub_self]
